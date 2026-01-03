using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Windows.Forms;
using System.Drawing;
using System.Drawing.Drawing2D;
using Quicker.Public;
using System.Threading.Tasks;
using System.Diagnostics;
using System.Text.RegularExpressions;
using System.Windows.Automation;

public static void Exec(IStepContext context)
{
    bool isDev = File.Exists(@"f:\桌面\开发\WindowLayoutProject\WindowLayoutManager.cs");

    if (isDev)
    {
        Logger.Init(@"f:\桌面\开发\WindowLayoutProject\WindowLayout.log");
        Logger.Log("==================================================");
        Logger.Log(">>> 开发者模式已识别：日志模块启动");
        Logger.Log($">>> 算法进化：响应式动态填坑算法 V4 (True Gap-Filler)");
    }

    try
    {
        bool instantMode = context.GetVarValue("instantMode")?.ToString().ToLower() == "true";
        int.TryParse(context.GetVarValue("autoExitSeconds")?.ToString(), out int autoExitSeconds);
        
        BlacklistManager.Reload();

        if (OverlayForm.Instance != null && !OverlayForm.Instance.IsDisposed && OverlayForm.Instance.Visible)
        {
            Logger.Log(">>> 触发已有实例热刷新");
            OverlayForm.Instance.Invoke((MethodInvoker)delegate {
                OverlayForm.Instance.TriggerManualRefresh();
                if (instantMode) OverlayForm.Instance.Close(); 
                else OverlayForm.Instance.Activate();
            });
            return;
        }

        var wins = WindowHelper.GetFilterWindows();
        Logger.Log($"[Filter-Done] 识别到参与排版的独立窗口数量: {wins.Count}");

        if (wins.Count == 0) return;

        if (instantMode)
        {
            Rectangle wa = Screen.PrimaryScreen.WorkingArea;
            var locks = LockManager.Load();
            var lockedItemMatches = new Dictionary<IntPtr, Rectangle>();
            var normalItems = new List<IntPtr>();
            var usedLocks = new HashSet<LockInfo>();

            foreach (var hwnd in wins)
            {
                var exactMatch = locks.Where(l => !usedLocks.Contains(l)).FirstOrDefault(l => LockManager.IsMatchStrict(hwnd, l));
                if (exactMatch != null) { lockedItemMatches[hwnd] = exactMatch.Rect; usedLocks.Add(exactMatch); }
                else normalItems.Add(hwnd);
            }

            if (normalItems.Count > 0) { Random rng = new Random(); normalItems = normalItems.OrderBy(x => rng.Next()).ToList(); }

            var assignment = LayoutAlgorithm.AssignSmartGaps(wa, lockedItemMatches, normalItems);
            foreach (var kvp in assignment) { if (WindowHelper.IsWindow(kvp.Key)) WindowHelper.MoveWindowCompensated(kvp.Key, kvp.Value); }
            return;
        }

        Rectangle workArea = Screen.PrimaryScreen.WorkingArea;
        var overlay = new OverlayForm(wins, workArea, autoExitSeconds);
        Application.Run(overlay);
    }
    catch (Exception ex)
    {
        Logger.Log($"[Critical] {ex.ToString()}");
        context.SetVarValue("errMessage", ex.Message);
    }
}

public class OverlayForm : Form
{
    private FlowLayoutPanel _sceneGallery;
    private Panel _galleryOverlay;

    public static OverlayForm Instance { get; private set; }
    private List<IntPtr> _windows;
    public List<LockInfo> _locks;
    private Rectangle _workArea;
    private Button _refreshBtn;
    private Button _confirmBtn;
    private Panel _iconContainer;
    private ToolTip _toolTip;
    private int _shuffleOffset = 0;
    private bool _locksDirty = false;
    private System.Windows.Forms.Timer _saveTimer;
    private System.Windows.Forms.Timer _autoExitTimer;
    private delegate void WinEventDelegate(IntPtr hWinEventHook, uint eventType, IntPtr hwnd, int idObject, int idChild, uint dwEventThread, uint dwmsEventTime);
    private WinEventDelegate _winEventDelegate;
    private IntPtr _hHook;

    [DllImport("user32.dll")] static extern IntPtr SetWinEventHook(uint eventMin, uint eventMax, IntPtr hmodWinEventProc, WinEventDelegate lpfnWinEventProc, uint idProcess, uint idThread, uint dwFlags);
    [DllImport("user32.dll")] static extern bool UnhookWinEvent(IntPtr hWinEventHook);
    [DllImport("user32.dll")] static extern bool SetWindowPos(IntPtr hWnd, IntPtr hWndInsertAfter, int X, int Y, int cx, int cy, uint uFlags);

    static readonly IntPtr HWND_TOPMOST = new IntPtr(-1);
    const uint SWP_NOMOVE = 0x0002;
    const uint SWP_NOSIZE = 0x0001;
    const uint SWP_SHOWWINDOW = 0x0040;

    private const uint EVENT_OBJECT_LOCATIONCHANGE = 0x800B;
    private const uint WINEVENT_OUTOFCONTEXT = 0;

    public OverlayForm(List<IntPtr> windows, Rectangle workArea, int autoExitSeconds)
    {
        Instance = this;
        this.Text = "Quicker_WindowLayoutOverlay_Host"; 
        this.AllowTransparency = true;
        this.SetStyle(ControlStyles.ResizeRedraw | ControlStyles.AllPaintingInWmPaint | ControlStyles.UserPaint, true);
        this.UpdateStyles();
        this.Opacity = 0; // 初始隐藏，防止闪烁

        _windows = windows;
        _workArea = workArea;
        _locks = LockManager.Load();
        _toolTip = new ToolTip { InitialDelay = 200, AutoPopDelay = 10000 };
        
        this.FormBorderStyle = FormBorderStyle.None;
        this.Bounds = workArea; // 直接指定边界，不使用 Maximized 以减少黑屏概率
        this.BackColor = Color.Magenta;
        this.TransparencyKey = Color.Magenta; 
        this.TopMost = true; 
        this.ShowInTaskbar = false;
        
        // 强制置顶
        SetWindowPos(this.Handle, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_SHOWWINDOW);
        
        this.Deactivate += (s, e) => { if (!this.ContainsFocus && !this.Capture) this.Close(); };

        this.KeyPreview = true;
        this.KeyDown += (s, e) => { if (e.KeyCode == Keys.Escape) this.Close(); };

        if (autoExitSeconds > 0)
        {
            _autoExitTimer = new System.Windows.Forms.Timer { Interval = autoExitSeconds * 1000 };
            _autoExitTimer.Tick += (s, e) => this.Close();
            _autoExitTimer.Start();
        }

        _iconContainer = new Panel { Dock = DockStyle.Fill, BackColor = Color.Transparent };
        this.Controls.Add(_iconContainer);

        this.Shown += (s, e) => { this.Opacity = 1; }; // 准备好了再亮相
        
        CreateControlButtons(); 
        PerformReLayout();

        _winEventDelegate = new WinEventDelegate(WinEventProc);
        _hHook = SetWinEventHook(EVENT_OBJECT_LOCATIONCHANGE, EVENT_OBJECT_LOCATIONCHANGE, IntPtr.Zero, _winEventDelegate, 0, 0, WINEVENT_OUTOFCONTEXT);

        _saveTimer = new System.Windows.Forms.Timer { Interval = 500 };
        _saveTimer.Tick += (s, e) => { if (_locksDirty) { LockManager.Save(_locks); _locksDirty = false; } };
        _saveTimer.Start();
    }
    
    public async void TriggerManualRefresh()
    {
        BlacklistManager.Reload();
        var latestWindows = WindowHelper.GetFilterWindows();
        _windows = latestWindows;
        this.Opacity = 0;
        await Task.Delay(20); 
        _shuffleOffset++; 
        PerformReLayout(); 
        this.Opacity = 1;
        SetWindowPos(this.Handle, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_SHOWWINDOW);
        _refreshBtn.BringToFront(); _confirmBtn.BringToFront();
        if (_autoExitTimer != null) { _autoExitTimer.Stop(); _autoExitTimer.Start(); }
    }

    private void WinEventProc(IntPtr hWinEventHook, uint eventType, IntPtr hwnd, int idObject, int idChild, uint dwEventThread, uint dwmsEventTime)
    {
        // 增加对当前窗口标题的实时过滤，防止扫描到自己
        if (idObject == 0 && _windows.Contains(hwnd) && this.Opacity > 0.1) 
        {
            this.Invoke((MethodInvoker)delegate { UpdateLockBtnPositionByHandle(hwnd); });
        }
    }

    private void UpdateLockBtnPositionByHandle(IntPtr hwnd)
    {
        foreach (Control c in _iconContainer.Controls)
        {
            if (c is LockButton btn && btn.Hwnd == hwnd)
            {
                Rectangle oldRect = btn.Bounds;
                Rectangle r = WindowHelper.GetVisibleRect(hwnd);
                if (oldRect.X == r.Left + 5 && oldRect.Y == r.Top + 5) return; // 位置没变，不处理

                btn.SetPositionByWindow(r);
                
                // 【核心：消除残影】通知窗体重画旧区域和新区域
                this.Invalidate(oldRect);
                this.Invalidate(btn.Bounds);
                this.Update(); // 立即执行重绘消息
                
                if (btn.IsLocked)
                {
                    var lockInfo = _locks.FirstOrDefault(l => LockManager.IsMatchStrict(hwnd, l));
                    if (lockInfo != null && lockInfo.Rect != r) { lockInfo.Rect = r; _locksDirty = true; }
                }
                break;
            }
        }
    }

    protected override void OnFormClosing(FormClosingEventArgs e)
    {
        this.FormClosed += (s, args) => { 
            if (_hHook != IntPtr.Zero) UnhookWinEvent(_hHook); 
            if (OverlayForm.Instance == this) OverlayForm.Instance = null;
        };
        _toolTip.Dispose();
        if (_locksDirty) LockManager.Save(_locks);
        base.OnFormClosing(e);
    }

    private void CreateControlButtons()
    {
        int btnSize = 40; int spacing = 20;
        int centerX = _workArea.X + (_workArea.Width / 2);
        int centerY = _workArea.Y + (_workArea.Height - btnSize) / 2;

        // 刷新按钮 (左)
        _refreshBtn = new Button {
            Size = new Size(btnSize, btnSize),
            Location = new Point(centerX - btnSize - btnSize/2 - spacing, centerY),
            FlatStyle = FlatStyle.Flat, BackColor = Color.FromArgb(180, 40, 40, 40), ForeColor = Color.White,
            Text = "↻", Font = new Font("Segoe UI Symbol", 18, FontStyle.Bold), Cursor = Cursors.Hand
        };
        _refreshBtn.FlatAppearance.BorderSize = 0;
        GraphicsPath p1 = new GraphicsPath(); p1.AddEllipse(0, 0, btnSize, btnSize); _refreshBtn.Region = new Region(p1);
        _refreshBtn.Click += (s, e) => { TriggerManualRefresh(); this.Activate(); };
        this.Controls.Add(_refreshBtn);

        // 相机按钮 (中)
        var _sceneSaveBtn = new Button {
            Size = new Size(btnSize, btnSize),
            Location = new Point(centerX - btnSize/2, centerY),
            FlatStyle = FlatStyle.Flat, BackColor = Color.FromArgb(180, 20, 20, 20), ForeColor = Color.FromArgb(52, 152, 219),
            Text = "📸", Font = new Font("Segoe UI Symbol", 18, FontStyle.Bold), Cursor = Cursors.Hand, Name = "SceneBtn"
        };
        _sceneSaveBtn.FlatAppearance.BorderSize = 0;
        GraphicsPath p3 = new GraphicsPath(); p3.AddEllipse(0, 0, btnSize, btnSize); _sceneSaveBtn.Region = new Region(p3);
        _sceneSaveBtn.Click += (s, e) => { 
            string name = DateTime.Now.ToString("MM-dd HHmmss") + " 布局";
            Logger.Log($"[SaveScene] >>> 开始执行快照保存: {name}");
            
            // 重要：不再只保存 _locks，而是保存当前所有 _windows 句柄的状态
            var snapshot = new List<LockInfo>();
            foreach (var h in _windows) {
                if (!WindowHelper.IsWindow(h)) continue;
                var info = new LockInfo {
                    ProcessName = LockManager.GetProcessName(h),
                    Title = WindowHelper.GetWindowTitle(h),
                    MatchKey = WindowHelper.GetSmartMatchKey(h),
                    Rect = WindowHelper.GetVisibleRect(h),
                    ExecPath = WindowHelper.GetExecutablePath(h)
                };
                if (info.ProcessName == "msedge" || info.ProcessName == "chrome") {
                    info.Url = WindowHelper.GetBrowserUrl(h);
                    Logger.Log($"[SaveScene-Debug] 浏览器 URL 抓取: {info.Title} -> {(string.IsNullOrEmpty(info.Url) ? "失败" : info.Url)}");
                }
                else if (info.ProcessName == "explorer") {
                    info.Url = WindowHelper.GetExplorerPath(h);
                    Logger.Log($"[SaveScene-Debug] 资源管理器路径抓取: {info.Title} -> {(string.IsNullOrEmpty(info.Url) ? "失败" : info.Url)}");
                }
                snapshot.Add(info);
            }

            SceneManager.SaveScene(name, snapshot);
            MessageBox.Show($"场景 [{name}] 已保存！（包含 {snapshot.Count} 个窗口）");
            
            this.Activate(); 
        };
        _sceneSaveBtn.MouseDown += (s, e) => {
            if (e.Button == MouseButtons.Right) {
                ShowSceneGallery();
                this.Activate();
            }
        };

        this.Controls.Add(_sceneSaveBtn);
        this._toolTip.SetToolTip(_sceneSaveBtn, "左键：保存当前场景\r\n右键：加载已有场景");

        // 确认按钮 (右)
        _confirmBtn = new Button {
            Size = new Size(btnSize, btnSize),
            Location = new Point(centerX + btnSize/2 + spacing, centerY),
            FlatStyle = FlatStyle.Flat, BackColor = Color.FromArgb(200, 20, 20, 20), ForeColor = Color.FromArgb(46, 204, 113),
            Text = "✔", Font = new Font("Segoe UI Symbol", 18, FontStyle.Bold), Cursor = Cursors.Hand
        };
        _confirmBtn.FlatAppearance.BorderSize = 0;
        GraphicsPath p2 = new GraphicsPath(); p2.AddEllipse(0, 0, btnSize, btnSize); _confirmBtn.Region = new Region(p2);
        _confirmBtn.Click += (s, e) => this.Close();
        this.Controls.Add(_confirmBtn);
    }

    private void ShowSceneGallery() {
        if (_galleryOverlay == null) {
            // 不再使用全屏遮罩，直接创建悬浮画廊容器
            _galleryOverlay = new Panel {
                Size = new Size(820, 500),
                BackColor = Color.FromArgb(255, 25, 25, 25),
                Location = new Point((this.Width - 820) / 2, (this.Height - 500) / 2),
                Visible = false
            };
            GraphicsPath path = new GraphicsPath(); 
            int r = 20; path.AddArc(0, 0, r, r, 180, 90); path.AddArc(_galleryOverlay.Width - r, 0, r, r, 270, 90);
            path.AddArc(_galleryOverlay.Width - r, _galleryOverlay.Height - r, r, r, 0, 90); path.AddArc(0, _galleryOverlay.Height - r, r, r, 90, 90);
            _galleryOverlay.Region = new Region(path);
            
            var title = new Label {
                Text = "🎬 我的布局场境 (右键管理)", ForeColor = Color.White, 
                Font = new Font("微软雅黑", 14, FontStyle.Bold),
                Location = new Point(30, 20), AutoSize = true
            };
            _galleryOverlay.Controls.Add(title);

            // 关闭按钮
            var closeBtn = new Label {
                Text = "✕", ForeColor = Color.Gray, Font = new Font("Segoe UI", 14, FontStyle.Bold),
                Location = new Point(780, 10), AutoSize = true, Cursor = Cursors.Hand
            };
            closeBtn.Click += (s, e) => { _galleryOverlay.Visible = false; };
            closeBtn.MouseEnter += (s, e) => { closeBtn.ForeColor = Color.White; };
            closeBtn.MouseLeave += (s, e) => { closeBtn.ForeColor = Color.Gray; };
            _galleryOverlay.Controls.Add(closeBtn);

            _sceneGallery = new FlowLayoutPanel {
                Location = new Point(20, 60), Size = new Size(780, 420),
                AutoScroll = true, BackColor = Color.Transparent
            };
            _galleryOverlay.Controls.Add(_sceneGallery);
            this.Controls.Add(_galleryOverlay);
        }

        _sceneGallery.Controls.Clear();
        var all = SceneManager.LoadAll();
        if (all.Count == 0) {
            _sceneGallery.Controls.Add(new Label { Text = "空空如也，快去点击 📸 保存一个吧！", ForeColor = Color.Gray, AutoSize = true, Margin = new Padding(30) });
        }

        foreach (var s in all) {
            var card = new Panel { Size = new Size(240, 180), Margin = new Padding(10), BackColor = Color.FromArgb(40, 40, 40), Cursor = Cursors.Hand };
            
            PictureBox pic = new PictureBox {
                Size = new Size(220, 130), Location = new Point(10, 10),
                SizeMode = PictureBoxSizeMode.Zoom, BackColor = Color.Black
            };
            if (File.Exists(s.ThumbnailPath)) pic.Image = Image.FromFile(s.ThumbnailPath);

            Label name = new Label {
                Text = s.Name, ForeColor = Color.White, TextAlign = ContentAlignment.MiddleCenter,
                Size = new Size(240, 30), Location = new Point(0, 145), Font = new Font("微软雅黑", 9)
            };

            card.Controls.Add(pic); card.Controls.Add(name);
            
            // 交互设置
            pic.Click += async (send, args) => { _galleryOverlay.Visible = false; await SceneManager.ApplyScene(s); };
            name.Click += async (send, args) => { _galleryOverlay.Visible = false; await SceneManager.ApplyScene(s); };
            card.Click += async (send, args) => { _galleryOverlay.Visible = false; await SceneManager.ApplyScene(s); };
            
            // Hover 变色
            card.MouseEnter += (send, args) => { card.BackColor = Color.FromArgb(70, 70, 70); };
            card.MouseLeave += (send, args) => { card.BackColor = Color.FromArgb(40, 40, 40); };

            // 右键菜单管理
            ContextMenuStrip cm = new ContextMenuStrip();
            var currentCard = card; // 捕获当前卡片引用
            var currentScene = s;   // 捕获当前场景引用
            cm.Items.Add("🗑️ 删除此场景", null, (send, args) => { 
                var list = SceneManager.LoadAll(); 
                list.RemoveAll(x => x.Name == currentScene.Name);
                if (File.Exists(currentScene.ThumbnailPath)) try { File.Delete(currentScene.ThumbnailPath); } catch{}
                string scenesFile = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "Quicker", "LayoutScenes", "WindowLayoutScenes.json");
                File.WriteAllText(scenesFile, Newtonsoft.Json.JsonConvert.SerializeObject(list));
                // 直接移除卡片
                _sceneGallery.Controls.Remove(currentCard);
                currentCard.Dispose();
                // 如果没有场景了，显示提示
                if (_sceneGallery.Controls.Count == 0) {
                    _sceneGallery.Controls.Add(new Label { Text = "空空如也，快去点击 📸 保存一个吧！", ForeColor = Color.Gray, AutoSize = true, Margin = new Padding(30) });
                }
            });
            cm.Items.Add("🧼 全部清空", null, (send, args) => { 
                SceneManager.Clear(); 
                _sceneGallery.Controls.Clear();
                _sceneGallery.Controls.Add(new Label { Text = "空空如也，快去点击 📸 保存一个吧！", ForeColor = Color.Gray, AutoSize = true, Margin = new Padding(30) });
            });
            card.ContextMenuStrip = cm;

            _sceneGallery.Controls.Add(card);
        }

        _galleryOverlay.Visible = true;
        _galleryOverlay.BringToFront();
    }

    private void PerformReLayout()
    {
        var lockedItemMatches = new Dictionary<IntPtr, Rectangle>();
        var normalItems = new List<IntPtr>();
        var usedLocks = new HashSet<LockInfo>();

        foreach (var hwnd in _windows)
        {
            var exactMatch = _locks.Where(l => !usedLocks.Contains(l)).FirstOrDefault(l => LockManager.IsMatchStrict(hwnd, l));
            if (exactMatch != null) { lockedItemMatches[hwnd] = exactMatch.Rect; usedLocks.Add(exactMatch); }
            else normalItems.Add(hwnd);
        }

        if (normalItems.Count > 0)
        {
            int offset = _shuffleOffset % normalItems.Count;
            normalItems = normalItems.Skip(offset).Concat(normalItems.Take(offset)).ToList();
        }

        var assignment = LayoutAlgorithm.AssignSmartGaps(_workArea, lockedItemMatches, normalItems);
        foreach (var kvp in assignment) { if (WindowHelper.IsWindow(kvp.Key)) WindowHelper.MoveWindowCompensated(kvp.Key, kvp.Value); }
        RebuildUI(assignment, lockedItemMatches.Keys.ToHashSet());
    }

    private void RebuildUI(Dictionary<IntPtr, Rectangle> assignment, HashSet<IntPtr> actuallyLockedHwnds)
    {
        _iconContainer.SuspendLayout();
        _iconContainer.Controls.Clear();
        foreach (var kvp in assignment)
        {
            IntPtr hwnd = kvp.Key;
            if (!WindowHelper.IsWindow(hwnd)) continue;
            var btn = new LockButton(hwnd, kvp.Value);
            bool isLocked = actuallyLockedHwnds.Contains(hwnd);
            btn.UpdateIcon(isLocked);
            btn.Click += (s, e) => { ToggleLock(btn); this.Activate(); if (_autoExitTimer != null) { _autoExitTimer.Stop(); _autoExitTimer.Start(); } };
            
            string title = WindowHelper.GetWindowTitle(hwnd);
            string proc = LockManager.GetProcessName(hwnd);
            _toolTip.SetToolTip(btn, $"[{proc}]\r\n{title}");

            ContextMenuStrip cm = new ContextMenuStrip();
            cm.Items.Add($"🚫 永久忽略 [{proc}]", null, (sender, args) => {
               if(MessageBox.Show($"确定要忽略 [{proc}] 吗？", "加入黑名单", MessageBoxButtons.YesNo) == DialogResult.Yes) { BlacklistManager.Add(proc); this.TriggerManualRefresh(); }
               this.Activate();
            });
            cm.Items.Add(new ToolStripSeparator());
            cm.Items.Add("📜 管理黑名单", null, (sender, args) => { BlacklistManager.OpenEditor(); this.Activate(); });
            btn.ContextMenuStrip = cm;
            _iconContainer.Controls.Add(btn);
            
            // 添加拖拽手柄按钮（在锁按钮右侧）
            var dragHandle = new DragHandle(hwnd, kvp.Value, btn);
            _toolTip.SetToolTip(dragHandle, "拖拽到另一个手柄可交换窗口位置");
            _iconContainer.Controls.Add(dragHandle);
        }
        _iconContainer.ResumeLayout();
        
        // 关键修复：确保所有控制按钮永远在图标容器之上
        foreach(Control c in this.Controls) {
            if (c != _iconContainer) c.BringToFront();
        }
    }

    private void ToggleLock(LockButton btn)
    {
        string pName = LockManager.GetProcessName(btn.Hwnd);
        string title = WindowHelper.GetWindowTitle(btn.Hwnd);
        string matchKey = WindowHelper.GetSmartMatchKey(btn.Hwnd);
        
        var existing = _locks.FirstOrDefault(l => LockManager.IsMatchStrict(btn.Hwnd, l));
        if (existing == null) {
            Rectangle realRect = WindowHelper.GetVisibleRect(btn.Hwnd);
            _locks.Add(new LockInfo { ProcessName = pName, Title = title, MatchKey = matchKey, Rect = realRect });
            btn.UpdateIcon(true);
        }
        else { _locks.Remove(existing); btn.UpdateIcon(false); }
        LockManager.Save(_locks);
    }
}

public class LockButton : Label {
    public IntPtr Hwnd; public Rectangle CurrentWindowRect; public bool IsLocked;
    
    public LockButton(IntPtr h, Rectangle r) {
        Hwnd = h; Size = new Size(32,32); Cursor = Cursors.Hand; TextAlign = ContentAlignment.MiddleCenter;
        Font = new Font("Segoe UI Emoji", 12); SetPositionByWindow(r);
    }
    
    public void SetPositionByWindow(Rectangle r) { CurrentWindowRect = r; this.Location = new Point(r.Left + 5, r.Top + 5); }
    
    public void UpdateIcon(bool locked) { 
        IsLocked = locked; 
        if (locked) {
            Text = "🔒"; 
            ForeColor = Color.White; 
            BackColor = Color.FromArgb(220, 46, 204, 113); // 锁定：翡翠绿背景
        } else {
            Text = "🔓";
            ForeColor = Color.Black; 
            BackColor = Color.FromArgb(220, 220, 220, 220); // 未锁：浅灰色背景
        }
    }
}

public class DragHandle : Label {
    public IntPtr Hwnd;
    public LockButton LinkedLock;
    
    private bool _isDragging = false;
    private Point _dragStartPoint;
    private Point _originalLocation;
    private static DragHandle _dragSource = null;
    
    public DragHandle(IntPtr h, Rectangle r, LockButton lockBtn) {
        Hwnd = h;
        LinkedLock = lockBtn;
        Size = new Size(20, 32);
        Cursor = Cursors.SizeAll;
        TextAlign = ContentAlignment.MiddleCenter;
        Font = new Font("Consolas", 10, FontStyle.Bold);
        Text = "⋮";
        ForeColor = Color.White;
        BackColor = Color.FromArgb(180, 149, 165, 166); // 银灰色
        Location = new Point(r.Left + 40, r.Top + 5); // 在锁按钮右侧
        
        this.MouseDown += DragHandle_MouseDown;
        this.MouseMove += DragHandle_MouseMove;
        this.MouseUp += DragHandle_MouseUp;
    }
    
    public void SetPositionByWindow(Rectangle r) {
        this.Location = new Point(r.Left + 40, r.Top + 5);
    }
    
    private void DragHandle_MouseDown(object sender, MouseEventArgs e) {
        if (e.Button == MouseButtons.Left) {
            _dragStartPoint = e.Location;
            _originalLocation = this.Location;
        }
    }
    
    private void DragHandle_MouseMove(object sender, MouseEventArgs e) {
        if (e.Button == MouseButtons.Left) {
            // 判断是否开始拖拽（移动超过 3 像素）
            if (!_isDragging && (Math.Abs(e.X - _dragStartPoint.X) > 3 || Math.Abs(e.Y - _dragStartPoint.Y) > 3)) {
                _isDragging = true;
                _dragSource = this;
                this.BackColor = Color.FromArgb(220, 52, 152, 219); // 拖拽时：蓝色
                this.BringToFront();
            }
            
            if (_isDragging) {
                this.Left += e.X - _dragStartPoint.X;
                this.Top += e.Y - _dragStartPoint.Y;
            }
        }
    }
    
    private void DragHandle_MouseUp(object sender, MouseEventArgs e) {
        if (_isDragging && _dragSource == this) {
            _isDragging = false;
            _dragSource = null;
            
            // 查找目标（鼠标下方的其他拖拽手柄或锁按钮）
            Point screenPos = this.PointToScreen(e.Location);
            DragHandle target = null;
            
            foreach (Control c in this.Parent.Controls) {
                if (c is DragHandle dh && dh != this) {
                    Rectangle dhScreen = dh.RectangleToScreen(dh.ClientRectangle);
                    if (dhScreen.Contains(screenPos)) {
                        target = dh;
                        break;
                    }
                }
                // 也检测锁按钮
                if (c is LockButton lb && lb != this.LinkedLock) {
                    Rectangle lbScreen = lb.RectangleToScreen(lb.ClientRectangle);
                    if (lbScreen.Contains(screenPos)) {
                        // 找到对应的 DragHandle
                        foreach (Control cc in this.Parent.Controls) {
                            if (cc is DragHandle dh2 && dh2.LinkedLock == lb) {
                                target = dh2;
                                break;
                            }
                        }
                        break;
                    }
                }
            }
            
            if (target != null) {
                SwapWindowPositions(this, target);
            } else {
                this.Location = _originalLocation;
            }
            
            this.BackColor = Color.FromArgb(180, 149, 165, 166);
        }
    }
    
    private void SwapWindowPositions(DragHandle src, DragHandle dst) {
        Rectangle srcRect = WindowHelper.GetVisibleRect(src.Hwnd);
        Rectangle dstRect = WindowHelper.GetVisibleRect(dst.Hwnd);
        
        Logger.Log($"[Swap] 开始交换位置: {LockManager.GetProcessName(src.Hwnd)} <-> {LockManager.GetProcessName(dst.Hwnd)}");
        Logger.Log($"  - 源窗口: {srcRect}");
        Logger.Log($"  - 目标窗口: {dstRect}");
        
        // 交换窗口位置
        WindowHelper.MoveWindowCompensated(src.Hwnd, dstRect);
        WindowHelper.MoveWindowCompensated(dst.Hwnd, srcRect);
        
        // 更新锁按钮和拖拽手柄的位置
        src.LinkedLock.SetPositionByWindow(dstRect);
        dst.LinkedLock.SetPositionByWindow(srcRect);
        src.SetPositionByWindow(dstRect);
        dst.SetPositionByWindow(srcRect);
        
        // 交换内部记录
        src.LinkedLock.CurrentWindowRect = dstRect;
        dst.LinkedLock.CurrentWindowRect = srcRect;
        
        // 更新锁定信息
        if (OverlayForm.Instance != null) {
            var locks = OverlayForm.Instance._locks;
            var srcLock = locks.FirstOrDefault(l => LockManager.IsMatchStrict(src.Hwnd, l));
            var dstLock = locks.FirstOrDefault(l => LockManager.IsMatchStrict(dst.Hwnd, l));
            
            if (srcLock != null) srcLock.Rect = dstRect;
            if (dstLock != null) dstLock.Rect = srcRect;
            
            LockManager.Save(locks);
        }
        
        Logger.Log($"[Swap] 交换完成");
    }
}

public static class LayoutAlgorithm {
    private static string _lastLayoutLog = "";

    // 【算法升级 V4】全动态填补：彻底解决重叠
    public static Dictionary<IntPtr, Rectangle> AssignSmartGaps(Rectangle workArea, Dictionary<IntPtr, Rectangle> lockedWins, List<IntPtr> normals) {
        var res = new Dictionary<IntPtr, Rectangle>();
        List<Rectangle> gaps = new List<Rectangle> { workArea };

        // 1. 将所有锁定窗口物理占用的空间从总画布中剔除
        foreach (var kvp in lockedWins) {
            res[kvp.Key] = kvp.Value;
            var tempGaps = new List<Rectangle>();
            foreach (var g in gaps) tempGaps.AddRange(SubtractRectangle(g, kvp.Value));
            gaps = tempGaps.Where(r => r.Width > 50 && r.Height > 50).ToList();
        }

        // 减少此处的冗余日志
        string currentLog = $"Normals:{normals.Count}|Gaps:{gaps.Count}";
        if (currentLog != _lastLayoutLog) {
            _lastLayoutLog = currentLog;
            Logger.Log($"[Layout-V4] 锁定剔除完成，可用坑位: {gaps.Count} | 待填入: {normals.Count}");
        }

        if (normals.Count == 0) return res;

        // 2. 如果坑位不够，把最大的坑位切分
        while (gaps.Count < normals.Count && gaps.Count > 0) {
            gaps = gaps.OrderByDescending(r => r.Width * r.Height).ToList();
            Rectangle big = gaps[0]; gaps.RemoveAt(0);
            if (big.Width > big.Height) {
                gaps.Add(new Rectangle(big.X, big.Y, big.Width / 2, big.Height));
                gaps.Add(new Rectangle(big.X + big.Width / 2, big.Y, big.Width - big.Width / 2, big.Height));
            } else {
                gaps.Add(new Rectangle(big.X, big.Y, big.Width, big.Height / 2));
                gaps.Add(new Rectangle(big.X, big.Y + big.Height / 2, big.Width, big.Height - big.Height / 2));
            }
        }

        // 3. 按照面积从大到小排列坑位，依次填入普通窗口
        gaps = gaps.OrderByDescending(r => r.Width * r.Height).ToList();
        for (int i = 0; i < normals.Count; i++) {
            if (i < gaps.Count) res[normals[i]] = gaps[i];
            else if (gaps.Count > 0) res[normals[i]] = gaps[i % gaps.Count]; // 极端兜底：重叠
        }
        
        return res;
    }

    // 经典矩形剔除逻辑 (CSG)
    private static List<Rectangle> SubtractRectangle(Rectangle baseRect, Rectangle sub) {
        var results = new List<Rectangle>();
        Rectangle inter = Rectangle.Intersect(baseRect, sub);
        if (inter.IsEmpty) { results.Add(baseRect); return results; }

        if (inter.Top > baseRect.Top) results.Add(new Rectangle(baseRect.X, baseRect.Y, baseRect.Width, inter.Y - baseRect.Y));
        if (inter.Bottom < baseRect.Bottom) results.Add(new Rectangle(baseRect.X, inter.Bottom, baseRect.Width, baseRect.Bottom - inter.Bottom));
        if (inter.Left > baseRect.Left) results.Add(new Rectangle(baseRect.X, inter.Y, inter.X - baseRect.X, inter.Height));
        if (inter.Right < baseRect.Right) results.Add(new Rectangle(inter.Right, inter.Y, baseRect.Right - inter.Right, inter.Height));

        return results;
    }
}

public static class BlacklistManager {
    static string F = Environment.ExpandEnvironmentVariables(@"%AppData%\Quicker\WindowLayoutBlacklist.txt");
    private static HashSet<string> _cache;
    public static void Reload() {
        if (!File.Exists(F)) _cache = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        else _cache = new HashSet<string>(File.ReadAllLines(F).Where(x => !string.IsNullOrWhiteSpace(x)), StringComparer.OrdinalIgnoreCase);
    }
    public static bool Contains(string processName) { if (_cache == null) Reload(); return _cache.Contains(processName); }
    public static void Add(string processName) { if (_cache == null) Reload(); if (_cache.Contains(processName)) return; _cache.Add(processName); File.AppendAllLines(F, new[] { processName }); }
    public static void OpenEditor() { if (!File.Exists(F)) File.WriteAllText(F, ""); System.Diagnostics.Process.Start("notepad.exe", F); }
}

public static class WindowHelper {
    [DllImport("user32.dll")] public static extern bool IsWindow(IntPtr h);
    [DllImport("user32.dll")] public static extern bool IsWindowVisible(IntPtr h);
    [DllImport("user32.dll")] public static extern bool IsIconic(IntPtr h);
    [DllImport("user32.dll")] public static extern bool MoveWindow(IntPtr h, int x, int y, int w, int h2, bool b);
    [DllImport("user32.dll")] public static extern bool GetWindowRect(IntPtr h, out Rect r);
    [DllImport("dwmapi.dll")] public static extern int DwmGetWindowAttribute(IntPtr h, int a, out Rect r, int s);
    [DllImport("dwmapi.dll", EntryPoint = "DwmGetWindowAttribute")] public static extern int DwmGetCloaked(IntPtr h, int a, out int v, int s);
    [DllImport("user32.dll")] public static extern bool EnumWindows(EnumProc p, IntPtr l); public delegate bool EnumProc(IntPtr h, IntPtr l);
    [DllImport("user32.dll", CharSet = CharSet.Auto)] public static extern int GetWindowText(IntPtr h, StringBuilder s, int m);
    [DllImport("user32.dll", CharSet = CharSet.Auto)] public static extern int GetClassName(IntPtr h, StringBuilder s, int m);
    [DllImport("user32.dll")] public static extern int GetWindowLong(IntPtr h, int n);
    [DllImport("user32.dll")] public static extern IntPtr GetParent(IntPtr h);

    [StructLayout(LayoutKind.Sequential)] public struct Rect { public int Left, Top, Right, Bottom; }
    public static string GetWindowTitle(IntPtr hwnd) { StringBuilder sb = new StringBuilder(256); GetWindowText(hwnd, sb, 256); return sb.ToString(); }
    public static void MoveWindowCompensated(IntPtr hwnd, Rectangle targetVisible) {
        Rect logical, visible; GetWindowRect(hwnd, out logical);
        if (DwmGetWindowAttribute(hwnd, 9, out visible, Marshal.SizeOf(typeof(Rect))) != 0) { MoveWindow(hwnd, targetVisible.X, targetVisible.Y, targetVisible.Width, targetVisible.Height, true); return; }
        int dL = visible.Left - logical.Left, dT = visible.Top - logical.Top, dR = logical.Right - visible.Right, dB = logical.Bottom - visible.Bottom;
        MoveWindow(hwnd, targetVisible.X - dL, targetVisible.Y - dT, targetVisible.Width + dL + dR, targetVisible.Height + dT + dB, true);
    }
    public static Rectangle GetVisibleRect(IntPtr hwnd) {
        Rect v; if (DwmGetWindowAttribute(hwnd, 9, out v, Marshal.SizeOf(typeof(Rect))) == 0) return new Rectangle(v.Left, v.Top, v.Right - v.Left, v.Bottom - v.Top);
        Rect r; if (GetWindowRect(hwnd, out r)) return new Rectangle(r.Left, r.Top, r.Right - r.Left, r.Bottom - r.Top);
        return Rectangle.Empty;
    }
    [DllImport("oleacc.dll")] static extern int AccessibleObjectFromWindow(IntPtr hwnd, uint dwId, ref Guid riid, [MarshalAs(UnmanagedType.IUnknown)] out object ppvObject);

    public static string GetExecutablePath(IntPtr hwnd) {
        try {
            GetWindowThreadProcessId(hwnd, out int pid);
            return Process.GetProcessById(pid).MainModule.FileName;
        } catch { return ""; }
    }
    [DllImport("user32.dll")] static extern int GetWindowThreadProcessId(IntPtr h, out int p);

    // 获取资源管理器窗口当前浏览的文件夹路径
    public static string GetExplorerPath(IntPtr hwnd) {
        try {
            dynamic shell = Activator.CreateInstance(Type.GetTypeFromProgID("Shell.Application"));
            foreach (dynamic win in shell.Windows()) {
                if ((IntPtr)(long)win.HWND == hwnd) {
                    string path = win.Document.Folder.Self.Path;
                    return path ?? "";
                }
            }
        } catch { }
        return "";
    }

    public static string GetSmartMatchKey(IntPtr hwnd) {
        string pn = LockManager.GetProcessName(hwnd);
        string title = GetWindowTitle(hwnd);
        
        // 1. 针对浏览器，优先获取域名
        if (pn == "msedge" || pn == "chrome") {
            string url = GetBrowserUrl(hwnd);
            if (!string.IsNullOrEmpty(url)) {
                try { 
                    var match = Regex.Match(url, @"[a-zA-Z0-9][-a-zA-Z0-9]{0,62}(\.[a-zA-Z0-9][-a-zA-Z0-9]{0,62})+");
                    if (match.Success) return "domain:" + match.Value;
                } catch {}
            }
        }
        
        // 2. 否则进行标题清洗
        string cleanTitle = Regex.Replace(title, @"( 和另外 \d+ 个页面)? - .*$", "");
        cleanTitle = Regex.Replace(cleanTitle, @" - (Microsoft Edge|Google Chrome)$", "");
        return "title:" + cleanTitle.Trim();
    }

    public static string GetBrowserUrl(IntPtr hwnd) {
        // 使用托管 UI Automation API (参考 EqualFill.cs)
        try {
            AutomationElement root = AutomationElement.FromHandle(hwnd);
            if (root == null) return null;
            
            // 查找所有 Edit 控件
            var edits = root.FindAll(TreeScope.Descendants, new PropertyCondition(AutomationElement.ControlTypeProperty, ControlType.Edit));
            
            int count = 0;
            foreach (AutomationElement edit in edits) {
                if (count++ > 5) break; // 只检查前5个
                string val = null;
                
                // 尝试 ValuePattern
                if (edit.TryGetCurrentPattern(ValuePattern.Pattern, out object vPtrn)) {
                    val = ((ValuePattern)vPtrn).Current.Value;
                } else {
                    val = edit.Current.Name;
                }
                
                if (!string.IsNullOrEmpty(val)) {
                    // 简单验证是否像 URL
                    if (val.StartsWith("http") || val.StartsWith("file:") || (val.Contains(".") && !val.Contains(" "))) {
                        return val.StartsWith("http") ? val : (val.StartsWith("file:") ? val : "https://" + val);
                    }
                }
            }
        } catch { }
        
        // 回退：传统 IAccessible
        try {
            Guid guid = new Guid("{61873046-5153-11ce-9a88-00aa006f1a39}");
            object obj;
            if (AccessibleObjectFromWindow(hwnd, 0xFFFFFFFC, ref guid, out obj) == 0) {
                var acc = (IAccessible)obj;
                return FindUrlInAcc(acc);
            }
        } catch {}
        return null;
    }

    private static string FindUrlInAcc(IAccessible acc) {
        try {
            if (acc.accValue != null && acc.accValue.ToString().StartsWith("http")) return acc.accValue.ToString();
            for (int i = 1; i <= acc.accChildCount; i++) {
                if (acc.get_accChild(i) is IAccessible child) {
                    string res = FindUrlInAcc(child);
                    if (res != null) return res;
                }
            }
        } catch {}
        return null;
    }

    public static List<IntPtr> GetFilterWindows() {
        var rawList = new List<IntPtr>();
        EnumWindows((h, p) => {
            if (!IsWindow(h) || !IsWindowVisible(h) || IsIconic(h)) return true;
            int style = GetWindowLong(h, -16); 
            if ((style & 0x10000000) == 0) return true; 
            if (GetParent(h) != IntPtr.Zero) return true;
            
            int cl; if (DwmGetCloaked(h, 14, out cl, 4) == 0 && cl != 0) return true;
            Rectangle r = GetVisibleRect(h); if (r.Width < 100 || r.Height < 100) return true;
            
            StringBuilder sbT = new StringBuilder(256); GetWindowText(h, sbT, 256); string t = sbT.ToString();
            StringBuilder sbC = new StringBuilder(256); GetClassName(h, sbC, 256); string cn = sbC.ToString();
            string pn = LockManager.GetProcessName(h);
            
            // 只有在调试模式下且窗口列表有变动时才由外部控制是否记录（此处先扫描）
            if (string.IsNullOrEmpty(t) || t == "Program Manager" || t == "Quicker_WindowLayoutOverlay_Host" || cn.Contains("WindowsForms10.Window.8.app")) return true;
            // 采用更安全的实例判定，防止访问已销毁的实例句柄
            var inst = OverlayForm.Instance;
            if (inst != null && !inst.IsDisposed) {
                try { if (h == inst.Handle) return true; } catch { /* 忽略可能存在的瞬间销毁异常 */ }
            }
            
            if ((pn == "Quicker" || pn == "Typeless" || pn == "Antigravity") && (t == "Status" || t == "Quicker" || t == "NotificationsWindow" || t == "QuickerStarter")) return true;
            if (t == "Status" && r.X == 0 && r.Y == 0) return true;
            if (pn.StartsWith("PixPin", StringComparison.OrdinalIgnoreCase)) return true;
            if (cn == "Shell_TrayWnd" || cn == "WorkerW" || cn == "Progman") return true; 

            rawList.Add(h); return true;
        }, IntPtr.Zero);

        var finalMap = new Dictionary<string, IntPtr>();
        foreach (var h in rawList) {
            string key = LockManager.GetProcessName(h) + "|" + GetWindowTitle(h);
            if (finalMap.ContainsKey(key)) { if ((long)h > (long)finalMap[key]) finalMap[key] = h; } 
            else finalMap[key] = h;
        }
        var result = finalMap.Values.ToList();
        
        // 日志指纹逻辑：防止重复记录
        string currentFingerprint = string.Join(",", result.Select(h => h.ToString() + GetWindowTitle(h)));
        if (currentFingerprint != _lastFingerprint) {
            _lastFingerprint = currentFingerprint;
            Logger.Log($"[Filter-Done] 窗口列表变动，识别到参与排版的独立窗口数量: {result.Count}");
            foreach(var h in result) Logger.Log($"  - HWND:{h} | Proc:{LockManager.GetProcessName(h)} | Title:\"{GetWindowTitle(h)}\"");
        }
        
        return result;
    }
    private static string _lastFingerprint = "";
}

public class LockInfo { 
    public string ProcessName; public string Title; public string MatchKey; public Rectangle Rect; 
    public string ExecPath; public string Url;
    public override string ToString() => $"{ProcessName}|{Title}|{Rect.X},{Rect.Y},{Rect.Width},{Rect.Height}|{MatchKey}|{ExecPath}|{Url}"; 
}

public class SceneProfile {
    public string Name;
    public List<LockInfo> Items;
    public string ThumbnailPath;
}

public static class SceneManager {
    static string Root = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "Quicker", "LayoutScenes");
    static string F = Path.Combine(Root, "WindowLayoutScenes.json");
    
    public static void SaveScene(string name, List<LockInfo> currentSnapshot) {
        if (!Directory.Exists(Root)) Directory.CreateDirectory(Root);
        var all = LoadAll();
        all.RemoveAll(x => x.Name == name);

        string thumbName = $"thumb_{DateTime.Now.Ticks}.jpg";
        string thumbPath = Path.Combine(Root, thumbName);
        CaptureScreenshot(thumbPath);

        all.Add(new SceneProfile { Name = name, Items = currentSnapshot, ThumbnailPath = thumbPath });
        File.WriteAllText(F, Newtonsoft.Json.JsonConvert.SerializeObject(all, Newtonsoft.Json.Formatting.Indented));
        
        Logger.Log($"[SaveScene] 场景文件已保存至磁盘: {all.Count} 个历史场景");
        foreach(var item in currentSnapshot) Logger.Log($"  - 记录: {item.ProcessName} | T:\"{item.Title}\" | P:\"{item.ExecPath}\" | Url:\"{item.Url}\"");
    }

    private static void CaptureScreenshot(string path) {
        try {
            var bounds = Screen.PrimaryScreen.Bounds;
            using (var bmp = new Bitmap(bounds.Width, bounds.Height)) {
                using (var g = Graphics.FromImage(bmp)) {
                    g.CopyFromScreen(Point.Empty, Point.Empty, bounds.Size);
                }
                // 缩小为 160x90 的图标级别缩略图，节省空间
                using (var thumb = bmp.GetThumbnailImage(160, 90, null, IntPtr.Zero)) {
                    thumb.Save(path, System.Drawing.Imaging.ImageFormat.Jpeg);
                }
            }
        } catch {}
    }

    public static void Clear() { if(File.Exists(F)) File.Delete(F); if(Directory.Exists(Root)) { try { Directory.Delete(Root, true); } catch {} } }
    public static List<SceneProfile> LoadAll() {
        if (!File.Exists(F)) return new List<SceneProfile>();
        try { return Newtonsoft.Json.JsonConvert.DeserializeObject<List<SceneProfile>>(File.ReadAllText(F)); } catch { return new List<SceneProfile>(); }
    }

    public static Task ApplyScene(SceneProfile scene) {
        Logger.Log($"[ApplyScene] >>> 开始恢复场景: {scene.Name} (包含记录: {scene.Items.Count} 个)");
        var hwnds = WindowHelper.GetFilterWindows(); 
        
        // 打印当前布局实况
        Logger.Log($"[ApplyScene] --- 当前布局实况 (恢复前) ---");
        foreach(var h in hwnds) {
            var r = WindowHelper.GetVisibleRect(h);
            Logger.Log($"  - {LockManager.GetProcessName(h)} | Pos: {r.X},{r.Y},{r.Width}x{r.Height} | Title: \"{WindowHelper.GetWindowTitle(h)}\"");
        }
        
        Logger.Log($"[ApplyScene] 当前系统范围内待匹配窗口总数: {hwnds.Count}");

        int successCount = 0;
        foreach (var item in scene.Items) {
            var target = hwnds.FirstOrDefault(h => LockManager.IsMatchStrict(h, item));
            
            if (target != IntPtr.Zero) {
                Logger.Log($"[ApplyScene] [√] 匹配成功: {item.ProcessName} | \"{item.Title}\" -> 移动至 {item.Rect}");
                WindowHelper.MoveWindowCompensated(target, item.Rect);
                successCount++;
            } else if (!string.IsNullOrEmpty(item.ExecPath)) {
                Logger.Log($"[ApplyScene] [?] 窗口未找到，尝试自动化拉起: {item.ProcessName} | 路径: {item.ExecPath}");
                try {
                    string args = "";
                    if (!string.IsNullOrEmpty(item.Url)) {
                        if (item.ProcessName == "msedge" || item.ProcessName == "chrome") {
                            args = $"--new-window \"{item.Url}\"";
                        } else if (item.ProcessName == "explorer") {
                            args = $"\"{item.Url}\""; // 资源管理器直接用路径作为参数
                        }
                    }
                    Process.Start(item.ExecPath, args);
                    _ = Task.Run(async () => {
                        for (int i = 0; i < 20; i++) {
                            await Task.Delay(500);
                            var currentHwnds = WindowHelper.GetFilterWindows();
                            var h = currentHwnds.FirstOrDefault(wh => LockManager.IsMatchStrict(wh, item));
                            if (h != IntPtr.Zero) {
                                Logger.Log($"[ApplyScene-Async] [√] 延迟归位成功: {item.ProcessName}");
                                WindowHelper.MoveWindowCompensated(h, item.Rect);
                                break;
                            }
                        }
                    });
                } catch (Exception ex) {
                    Logger.Log($"[ApplyScene] [!] 拉起失败: {ex.Message}");
                }
            } else {
                 Logger.Log($"[ApplyScene] [X] 匹配失败且无路径可拉起: {item.ProcessName} | {item.Title}");
            }
        }
        Logger.Log($"[ApplyScene] <<< 恢复任务发送完毕，直接命中数: {successCount}");
        return Task.CompletedTask;
    }
}

[ComImport, Guid("61873046-5153-11ce-9a88-00aa006f1a39"), InterfaceType(ComInterfaceType.InterfaceIsIUnknown)]
public interface IAccessible {
    [DispId(-5000)] object accParent { get; }
    [DispId(-5001)] int accChildCount { get; }
    [DispId(-5003)] string accName { get; }
    [DispId(-5004)] string accValue { get; }
    [DispId(-5012)] object get_accChild(object childID);
}

public static class LockManager {
    static string F = Environment.ExpandEnvironmentVariables(@"%AppData%\Quicker\WindowLayoutLocks.txt");
    public static List<LockInfo> Load() => !File.Exists(F) ? new List<LockInfo>() : File.ReadAllLines(F).Select(l => {
        try { var p=l.Split('|'); if(p.Length < 3) return null; var r=p[2].Split(','); 
            var info = new LockInfo{ProcessName=p[0], Title=p[1], Rect=new Rectangle(int.Parse(r[0]),int.Parse(r[1]),int.Parse(r[2]),int.Parse(r[3]))};
            if (p.Length >= 4) info.MatchKey = p[3];
            return info;
        } catch{return null;}
    }).Where(x=>x!=null).ToList();
    public static void Save(List<LockInfo> l) { try { string tmp = F + ".tmp"; File.WriteAllLines(tmp, l.Select(x=>x.ToString())); if(File.Exists(F)) File.Delete(F); File.Move(tmp, F); } catch { } }
    
    public static bool IsMatchStrict(IntPtr h, LockInfo i) { 
        if (!string.Equals(GetProcessName(h), i.ProcessName, StringComparison.OrdinalIgnoreCase)) return false;
        
        // 资源管理器特殊处理：使用文件夹路径匹配
        if (i.ProcessName == "explorer" && !string.IsNullOrEmpty(i.Url)) {
            string currentPath = WindowHelper.GetExplorerPath(h);
            if (!string.IsNullOrEmpty(currentPath) && string.Equals(currentPath, i.Url, StringComparison.OrdinalIgnoreCase)) return true;
            return false; // 路径不匹配则直接失败
        }
        
        // 浏览器特殊处理：需要匹配 URL 或标题
        if (i.ProcessName == "msedge" || i.ProcessName == "chrome") {
            // 走后续的标题/MatchKey 匹配逻辑
        }
        // 其他单窗口应用（代码编辑器、普通软件等）：进程名相同即可匹配
        else {
            return true; // 直接匹配成功
        }
        
        string currentKey = WindowHelper.GetSmartMatchKey(h);
        string currentTitle = WindowHelper.GetWindowTitle(h);
        
        // 核心优化：清洗标题（剔除浏览器动态增加的后缀）
        string cleanCurrent = CleanTitle(currentTitle);
        string cleanSave = CleanTitle(i.Title);

        // 1. 尝试 MatchKey (精确域名匹配)
        if (!string.IsNullOrEmpty(i.MatchKey) && currentKey == i.MatchKey) return true;
        
        // 2. 尝试清洗后的标题完全匹配
        if (string.Equals(cleanCurrent, cleanSave, StringComparison.OrdinalIgnoreCase)) return true;

        // 3. 模糊包含（针对极端情况）
        if (!string.IsNullOrEmpty(cleanSave) && cleanCurrent.Contains(cleanSave)) return true;
        
        return false;
    }

    private static string CleanTitle(string t) {
        if (string.IsNullOrEmpty(t)) return "";
        // 剔除 "和另外 X 个页面"
        string res = System.Text.RegularExpressions.Regex.Replace(t, @" 和另外 \d+ 个页面.*$", "");
        // 剔除 " - Microsoft​ Edge" 或 " - Google Chrome"
        res = res.Replace(" - Microsoft​ Edge", "").Replace(" - Google Chrome", "");
        return res.Trim();
    }
    public static string GetProcessName(IntPtr h) { GetWindowThreadProcessId(h, out int pid); try { return System.Diagnostics.Process.GetProcessById(pid).ProcessName; } catch { return "Unknown"; } }
    [DllImport("user32.dll")] static extern int GetWindowThreadProcessId(IntPtr h, out int p);
}

public static class Logger {
    static string _p; public static void Init(string p) => _p=p;
    public static void Log(string m) { if (_p == null) return; try { File.AppendAllText(_p, $"[{DateTime.Now:HH:mm:ss}] {m}\r\n"); } catch {} }
}
