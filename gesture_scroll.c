// GestureScroll 1.0.3a (Unicode/W version)
// - Usage EDIT height = 300
// - Japanese UI strings: W APIs + L"..."
// - Hotkey toggle ON/OFF
// - Arm on full rotation (>= 360 deg), then scroll with smaller STEP (e.g., 90 deg)
// - ★NEW: Disarm when spinning stops (idle timeout) -> requires re-arm (>=360deg) again
// - Curvature gate (pathLen/chordLen) to reduce false positives
// - Tray icon ON/OFF colored, menu Japanese
// - INI W, startup shortcut create/remove (IShellLinkW)
// - Paint background with system theme (reduce black window after restore)
//
// Build notes:
// 1) Project Properties -> General -> Character Set: Use Unicode Character Set
// 2) To hide console: Linker -> System -> Subsystem: Windows (/SUBSYSTEM:WINDOWS)

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <shellapi.h>
#include <process.h>
#include <math.h>
#include <commctrl.h>

#include <shlobj.h>     // SHGetFolderPathW, CSIDL_STARTUP
#include <objbase.h>    // CoInitializeEx
#include <shobjidl.h>   // IShellLinkW
#include <strsafe.h>

#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "comctl32.lib")
#pragma comment(lib, "ole32.lib")

// ----------------------------
// Version / App
// ----------------------------
#define APP_NAME        L"SpinScroll"
#define APP_VERSION     L"1.0.4"
#define WIN_CLASS       L"SpinScrollMainWindow"
#define WM_TRAYICON     (WM_APP + 1)

#define STARTUP_LNK_NAME L"SpinScroll.lnk"

// ----------------------------
// Gesture Params (tuning knobs)
// ----------------------------
#define CENTER_ALPHA               0.1

// Start strict, then scroll lighter after arming
#define ARM_START_DEG              500.0    // 360..720 (more strict -> higher)
#define STEP_DEG_ARMED             60.0    // 60..180  (after arm)

#define MIN_SCROLL_INTERVAL_MS     50
#define MIN_CALC_INTERVAL_MS       20
#define MIN_RADIUS_PX              30.0
#define MIN_DDEG_THRESHOLD          3.0
#define MAX_STEPS_PER_TICK          2
#define MIN_MOVE_DIST2              9       // 3px^2

// Trigger tightening (Curvature Gate)
#define ARM_MIN_CHORD_PX           60.0    // 60..120
#define ARM_MIN_CURVATURE_RATIO     1.8    // 1.6..2.0+ (more strict -> higher)

// ★NEW: stop spinning -> disarm -> needs re-arm
#define DISARM_IDLE_MS             200     // 200..500

// ----------------------------
// UI IDs
// ----------------------------
#define IDC_USAGE_EDIT           101
#define IDC_STATUS_BOX           102
#define IDC_STATUS_TEXT          103
#define IDC_TOGGLE_BTN           104
#define IDC_INVERT_CHECK         105
#define IDC_HOTKEY_EDIT          106
#define IDC_HOTKEY_SET_BTN       107
#define IDC_APPLY_BTN            108
#define IDC_MINIMIZE_TRAY_BTN    109

#define IDC_SPEED_SLIDER         110
#define IDC_SPEED_TEXT           111

#define IDC_STARTMIN_CHECK       112   // 起動時にGUIを隠す
#define IDC_STARTUPSHORT_CHECK   113   // スタートアップへショートカット作成

#define IDM_TRAY_TOGGLE          201
#define IDM_TRAY_SHOW            202
#define IDM_TRAY_EXIT            203

// ----------------------------
// Hotkey
// ----------------------------
#define HOTKEY_ID_TOGGLE      1

typedef struct { LONG x; LONG y; } Pt;

typedef struct {
    int  active;                   // 0/1
    int  invert_direction;         // 0/1
    UINT hotkey_mods;              // MOD_CONTROL|MOD_ALT etc
    UINT hotkey_vk;                // 'S' etc
    int  scroll_notches_per_step;  // 1..10

    int  start_minimized;          // 0/1 : 起動時にGUIを隠してトレイ常駐
    int  startup_shortcut;         // 0/1 : スタートアップフォルダにlnkを置く
} AppConfig;

static AppConfig g_cfg = { 0 };

// runtime
static volatile LONG g_running = 1;
static volatile LONG g_active = 0;

// hooks/thread
static HHOOK  g_mouseHook = NULL;
static HANDLE g_workerThread = NULL;
static CRITICAL_SECTION g_cs;
static Pt g_latestPoint = { 0,0 };
static volatile LONG g_hasNewPoint = 0;

// gesture state
static int    g_hasPrev = 0;
static double g_cx = 0.0, g_cy = 0.0;
static int    g_hasAng = 0;
static double g_prevAng = 0.0;
static double g_accumDeg = 0.0;
static double g_totalAbsDeg = 0.0;
static ULONGLONG g_lastScrollTick = 0;
static ULONGLONG g_lastCalcTick = 0;

// Curvature tracking (pathLen/chordLen)
static double g_pathLen = 0.0;
static LONG   g_startX = 0, g_startY = 0;
static LONG   g_prevX = 0, g_prevY = 0;

// arming state
static int    g_armed = 0;

// ★NEW: last time we observed "spin-like" delta
static ULONGLONG g_lastSpinTick = 0;

// UI handles
static HWND g_hwnd = NULL;
static HWND g_usageEdit = NULL;
static HWND g_statusBox = NULL;
static HWND g_statusText = NULL;
static HWND g_toggleBtn = NULL;
static HWND g_invertCheck = NULL;
static HWND g_hotkeyEdit = NULL;
static HWND g_hotkeySetBtn = NULL;
static HWND g_applyBtn = NULL;
static HWND g_minTrayBtn = NULL;

static HWND g_speedSlider = NULL;
static HWND g_speedText = NULL;

static HWND g_startMinCheck = NULL;
static HWND g_startupShortcutCheck = NULL;

// tray/icon
static NOTIFYICONDATAW g_nid;
static HMENU g_trayMenu = NULL;
static HICON g_iconOn = NULL;
static HICON g_iconOff = NULL;

// hotkey capture mode
static int g_capturingHotkey = 0;

// ----------------------------
// Forward decl
// ----------------------------
static void apply_active(int on);
static void update_visuals(void);
static void load_config(AppConfig* cfg);
static void save_config(const AppConfig* cfg);
static void register_hotkey_from_cfg(HWND hwnd);
static void unregister_hotkey(HWND hwnd);
static void set_hotkey_text(HWND edit, UINT mods, UINT vk);

static int ensure_startup_shortcut(int want_present);
static int startup_shortcut_exists(void);

// ----------------------------
// INI path (W)
// ----------------------------
static void get_ini_path(wchar_t* out, size_t outsz) {
    wchar_t exePath[MAX_PATH];
    GetModuleFileNameW(NULL, exePath, MAX_PATH);

    StringCchCopyW(out, outsz, exePath);
    wchar_t* dot = wcsrchr(out, L'.');
    if (dot) {
        StringCchCopyW(dot, outsz - (dot - out), L".ini");
    }
    else {
        StringCchCatW(out, outsz, L".ini");
    }
}

// ----------------------------
// Create a solid-color icon at runtime (16x16)
// ----------------------------
static HICON create_solid_icon(COLORREF rgb) {
    const int W = 16, H = 16;

    BITMAPV5HEADER bi;
    ZeroMemory(&bi, sizeof(bi));
    bi.bV5Size = sizeof(bi);
    bi.bV5Width = W;
    bi.bV5Height = -H; // top-down
    bi.bV5Planes = 1;
    bi.bV5BitCount = 32;
    bi.bV5Compression = BI_BITFIELDS;
    bi.bV5RedMask = 0x00FF0000;
    bi.bV5GreenMask = 0x0000FF00;
    bi.bV5BlueMask = 0x000000FF;
    bi.bV5AlphaMask = 0xFF000000;

    void* bits = NULL;
    HDC hdc = GetDC(NULL);
    HBITMAP colorBmp = CreateDIBSection(hdc, (BITMAPINFO*)&bi, DIB_RGB_COLORS, &bits, NULL, 0);
    ReleaseDC(NULL, hdc);
    if (!colorBmp || !bits) return NULL;

    DWORD a = 0xFF000000;
    DWORD r = ((rgb >> 16) & 0xFF) << 16;
    DWORD g = ((rgb >> 8) & 0xFF) << 8;
    DWORD b = (rgb & 0xFF);
    DWORD px = a | r | g | b;

    DWORD* p = (DWORD*)bits;
    for (int i = 0; i < W * H; i++) p[i] = px;

    // ring for visibility
    for (int y = 1; y < H - 1; y++) {
        for (int x = 1; x < W - 1; x++) {
            int dx = x - 8, dy = y - 8;
            int d2 = dx * dx + dy * dy;
            if (d2 >= 36 && d2 <= 49) p[y * W + x] = 0xFFFFFFFF;
        }
    }

    HBITMAP maskBmp = CreateBitmap(W, H, 1, 1, NULL);

    ICONINFO ii;
    ZeroMemory(&ii, sizeof(ii));
    ii.fIcon = TRUE;
    ii.hbmColor = colorBmp;
    ii.hbmMask = maskBmp;

    HICON hIcon = CreateIconIndirect(&ii);

    DeleteObject(colorBmp);
    DeleteObject(maskBmp);
    return hIcon;
}

// ----------------------------
// Config load/save (W)
// ----------------------------
static void load_config(AppConfig* cfg) {
    cfg->active = 0;
    cfg->invert_direction = 0;
    cfg->hotkey_mods = MOD_CONTROL | MOD_ALT;
    cfg->hotkey_vk = 'S';
    cfg->scroll_notches_per_step = 1;

    cfg->start_minimized = 0;
    cfg->startup_shortcut = 0;

    wchar_t ini[MAX_PATH];
    get_ini_path(ini, _countof(ini));

    cfg->active = GetPrivateProfileIntW(L"main", L"active", cfg->active, ini);
    cfg->invert_direction = GetPrivateProfileIntW(L"main", L"invert_direction", cfg->invert_direction, ini);
    cfg->hotkey_mods = (UINT)GetPrivateProfileIntW(L"main", L"hotkey_mods", (int)cfg->hotkey_mods, ini);
    cfg->hotkey_vk = (UINT)GetPrivateProfileIntW(L"main", L"hotkey_vk", (int)cfg->hotkey_vk, ini);
    cfg->scroll_notches_per_step =
        GetPrivateProfileIntW(L"main", L"scroll_notches_per_step", cfg->scroll_notches_per_step, ini);

    cfg->start_minimized =
        GetPrivateProfileIntW(L"main", L"start_minimized", cfg->start_minimized, ini);

    cfg->startup_shortcut =
        GetPrivateProfileIntW(L"main", L"startup_shortcut", cfg->startup_shortcut, ini);

    if (cfg->hotkey_vk == 0) cfg->hotkey_vk = 'S';
    if (cfg->hotkey_mods == 0) cfg->hotkey_mods = MOD_CONTROL | MOD_ALT;

    if (cfg->scroll_notches_per_step < 1) cfg->scroll_notches_per_step = 1;
    if (cfg->scroll_notches_per_step > 10) cfg->scroll_notches_per_step = 10;

    cfg->start_minimized = cfg->start_minimized ? 1 : 0;
    cfg->startup_shortcut = cfg->startup_shortcut ? 1 : 0;
}

static void save_config(const AppConfig* cfg) {
    wchar_t ini[MAX_PATH];
    get_ini_path(ini, _countof(ini));

    wchar_t buf[64];

    StringCchPrintfW(buf, _countof(buf), L"%d", cfg->active);
    WritePrivateProfileStringW(L"main", L"active", buf, ini);

    StringCchPrintfW(buf, _countof(buf), L"%d", cfg->invert_direction);
    WritePrivateProfileStringW(L"main", L"invert_direction", buf, ini);

    StringCchPrintfW(buf, _countof(buf), L"%u", cfg->hotkey_mods);
    WritePrivateProfileStringW(L"main", L"hotkey_mods", buf, ini);

    StringCchPrintfW(buf, _countof(buf), L"%u", cfg->hotkey_vk);
    WritePrivateProfileStringW(L"main", L"hotkey_vk", buf, ini);

    StringCchPrintfW(buf, _countof(buf), L"%d", cfg->scroll_notches_per_step);
    WritePrivateProfileStringW(L"main", L"scroll_notches_per_step", buf, ini);

    StringCchPrintfW(buf, _countof(buf), L"%d", cfg->start_minimized);
    WritePrivateProfileStringW(L"main", L"start_minimized", buf, ini);

    StringCchPrintfW(buf, _countof(buf), L"%d", cfg->startup_shortcut);
    WritePrivateProfileStringW(L"main", L"startup_shortcut", buf, ini);
}

// ----------------------------
// Startup shortcut helpers (W)
// ----------------------------
static void get_startup_lnk_path(wchar_t* out, size_t outsz) {
    wchar_t folder[MAX_PATH];
    folder[0] = 0;
    SHGetFolderPathW(NULL, CSIDL_STARTUP, NULL, SHGFP_TYPE_CURRENT, folder);

    StringCchCopyW(out, outsz, folder);
    StringCchCatW(out, outsz, L"\\");
    StringCchCatW(out, outsz, STARTUP_LNK_NAME);
}

static int startup_shortcut_exists(void) {
    wchar_t path[MAX_PATH];
    get_startup_lnk_path(path, _countof(path));
    DWORD attr = GetFileAttributesW(path);
    return (attr != INVALID_FILE_ATTRIBUTES) ? 1 : 0;
}

static int create_startup_shortcut(void) {
    wchar_t lnkPath[MAX_PATH];
    get_startup_lnk_path(lnkPath, _countof(lnkPath));

    wchar_t exePath[MAX_PATH];
    GetModuleFileNameW(NULL, exePath, MAX_PATH);

    IShellLinkW* psl = NULL;
    HRESULT hr = CoCreateInstance(&CLSID_ShellLink, NULL, CLSCTX_INPROC_SERVER,
        &IID_IShellLinkW, (void**)&psl);
    if (FAILED(hr) || !psl) return 0;

    psl->lpVtbl->SetPath(psl, exePath);
    psl->lpVtbl->SetDescription(psl, L"GestureScroll startup shortcut");

    IPersistFile* ppf = NULL;
    hr = psl->lpVtbl->QueryInterface(psl, &IID_IPersistFile, (void**)&ppf);
    if (FAILED(hr) || !ppf) {
        psl->lpVtbl->Release(psl);
        return 0;
    }

    hr = ppf->lpVtbl->Save(ppf, lnkPath, TRUE);

    ppf->lpVtbl->Release(ppf);
    psl->lpVtbl->Release(psl);

    return SUCCEEDED(hr) ? 1 : 0;
}

static int remove_startup_shortcut(void) {
    wchar_t lnkPath[MAX_PATH];
    get_startup_lnk_path(lnkPath, _countof(lnkPath));
    if (!startup_shortcut_exists()) return 1;
    return DeleteFileW(lnkPath) ? 1 : 0;
}

static int ensure_startup_shortcut(int want_present) {
    if (want_present) {
        if (startup_shortcut_exists()) return 1;
        return create_startup_shortcut();
    }
    else {
        return remove_startup_shortcut();
    }
}

// ----------------------------
// Gesture core
// ----------------------------
static void reset_gesture_state(void) {
    g_hasPrev = 0;
    g_cx = 0.0; g_cy = 0.0;
    g_hasAng = 0;
    g_prevAng = 0.0;
    g_accumDeg = 0.0;
    g_totalAbsDeg = 0.0;
    g_lastScrollTick = 0;
    g_lastCalcTick = 0;

    g_pathLen = 0.0;
    g_startX = g_startY = 0;
    g_prevX = g_prevY = 0;

    g_armed = 0;
    g_lastSpinTick = 0;
}

static void clear_pending_point(void) {
    EnterCriticalSection(&g_cs);
    InterlockedExchange(&g_hasNewPoint, 0);
    LeaveCriticalSection(&g_cs);
}

static double rad_to_deg(double r) { return r * (180.0 / 3.14159265358979323846); }
static double wrap_deg(double d) {
    while (d > 180.0) d -= 360.0;
    while (d < -180.0) d += 360.0;
    return d;
}

static void send_wheel_steps(int direction_up, int steps) {
    if (steps <= 0) return;

    INPUT in;
    ZeroMemory(&in, sizeof(in));
    in.type = INPUT_MOUSE;
    in.mi.dwFlags = MOUSEEVENTF_WHEEL;

    int notches = g_cfg.scroll_notches_per_step;
    if (notches < 1) notches = 1;
    if (notches > 10) notches = 10;

    int delta = WHEEL_DELTA * notches * steps;
    in.mi.mouseData = direction_up ? delta : -delta;

    SendInput(1, &in, sizeof(in));
}

// Curvature gate: chord + ratio
static int curvature_gate_ok(LONG x, LONG y) {
    double cdx = (double)(x - g_startX);
    double cdy = (double)(y - g_startY);
    double chord = sqrt(cdx * cdx + cdy * cdy);
    if (chord < ARM_MIN_CHORD_PX) return 0;

    double ratio = (chord > 1.0) ? (g_pathLen / chord) : 0.0;
    if (ratio < ARM_MIN_CURVATURE_RATIO) return 0;

    return 1;
}

static void disarm_and_reseed(LONG x, LONG y, ULONGLONG now) {
    (void)now;
    g_armed = 0;

    // reset accumulators so normal mouse motion won't cause scroll
    g_accumDeg = 0.0;
    g_totalAbsDeg = 0.0;

    // reseed curvature tracking to avoid stale ratio
    g_pathLen = 0.0;
    g_startX = x; g_startY = y;
    g_prevX = x; g_prevY = y;

    // reseed angle baseline
    g_hasAng = 0;
    g_prevAng = 0.0;

    // "spin" timer reset
    g_lastSpinTick = 0;
}

static void process_point(LONG x, LONG y) {
    ULONGLONG now = GetTickCount64();

    // Throttle calc
    if (g_lastCalcTick != 0 && (now - g_lastCalcTick) < MIN_CALC_INTERVAL_MS) return;
    g_lastCalcTick = now;

    if (!g_hasPrev) {
        g_cx = (double)x; g_cy = (double)y;
        g_hasPrev = 1;

        g_startX = x; g_startY = y;
        g_prevX = x; g_prevY = y;
        g_pathLen = 0.0;

        g_hasAng = 0;
        g_accumDeg = 0.0;
        g_totalAbsDeg = 0.0;
        g_armed = 0;
        g_lastSpinTick = 0;
        return;
    }

    // ★NEW: armed中、一定時間 “回転らしい入力” が無ければ disarm（再アームが必要）
    if (g_armed && g_lastSpinTick != 0 && (now - g_lastSpinTick) > DISARM_IDLE_MS) {
        disarm_and_reseed(x, y, now);
        return;
    }

    // path length
    {
        double mdx = (double)(x - g_prevX);
        double mdy = (double)(y - g_prevY);
        g_pathLen += sqrt(mdx * mdx + mdy * mdy);
        g_prevX = x;
        g_prevY = y;
    }

    // center smoothing
    g_cx = (1.0 - CENTER_ALPHA) * g_cx + CENTER_ALPHA * (double)x;
    g_cy = (1.0 - CENTER_ALPHA) * g_cy + CENTER_ALPHA * (double)y;

    double dx = (double)x - g_cx;
    double dy = (double)y - g_cy;
    double r = sqrt(dx * dx + dy * dy);
    if (r < MIN_RADIUS_PX) return;

    double ang = atan2(dy, dx);

    if (!g_hasAng) {
        g_prevAng = ang;
        g_hasAng = 1;
        return;
    }

    double dAng = ang - g_prevAng;
    while (dAng > 3.14159265358979323846)  dAng -= 2.0 * 3.14159265358979323846;
    while (dAng < -3.14159265358979323846) dAng += 2.0 * 3.14159265358979323846;

    g_prevAng = ang;

    double dDeg = wrap_deg(rad_to_deg(dAng));
    if (fabs(dDeg) < MIN_DDEG_THRESHOLD) return;

    // we observed "spin-like" delta
    g_lastSpinTick = now;

    g_accumDeg += dDeg;
    g_totalAbsDeg += fabs(dDeg);

    // before arming: require >= 360 deg AND curvature gate
    if (!g_armed) {
        if (g_totalAbsDeg >= ARM_START_DEG && curvature_gate_ok(x, y)) {
            g_armed = 1;

            // prevent immediate burst after arming
            g_accumDeg = 0.0;
        }
        else {
            return;
        }
    }

    // after arming: scroll with small step
    if (g_lastScrollTick != 0 && (now - g_lastScrollTick) < MIN_SCROLL_INTERVAL_MS) return;

    int steps = (int)(fabs(g_accumDeg) / STEP_DEG_ARMED);
    if (steps <= 0) return;
    if (steps > MAX_STEPS_PER_TICK) steps = MAX_STEPS_PER_TICK;

    int direction_up = (g_accumDeg > 0.0) ? 1 : 0;
    if (g_cfg.invert_direction) direction_up = direction_up ? 0 : 1;

    send_wheel_steps(direction_up, steps);

    double consumed = (g_accumDeg > 0.0) ? (STEP_DEG_ARMED * steps) : (-STEP_DEG_ARMED * steps);
    g_accumDeg -= consumed;

    g_lastScrollTick = now;
}

// worker
static unsigned __stdcall WorkerThread(void* arg) {
    (void)arg;
    while (InterlockedCompareExchange(&g_running, 1, 1) == 1) {
        if (InterlockedCompareExchange(&g_active, 0, 0) == 1 &&
            InterlockedCompareExchange(&g_hasNewPoint, 0, 0) == 1) {

            Pt pt;
            EnterCriticalSection(&g_cs);
            pt = g_latestPoint;
            InterlockedExchange(&g_hasNewPoint, 0);
            LeaveCriticalSection(&g_cs);

            process_point(pt.x, pt.y);
        }
        Sleep(5);
    }
    return 0;
}

// mouse hook
static LRESULT CALLBACK LowLevelMouseProc(int nCode, WPARAM wParam, LPARAM lParam) {
    if (nCode == HC_ACTION && wParam == WM_MOUSEMOVE) {
        if (InterlockedCompareExchange(&g_active, 0, 0) == 1) {
            const MSLLHOOKSTRUCT* ms = (const MSLLHOOKSTRUCT*)lParam;

            static LONG lastX = 0, lastY = 0;
            LONG ddx = ms->pt.x - lastX;
            LONG ddy = ms->pt.y - lastY;

            if (ddx * ddx + ddy * ddy >= MIN_MOVE_DIST2) {
                EnterCriticalSection(&g_cs);
                g_latestPoint.x = ms->pt.x;
                g_latestPoint.y = ms->pt.y;
                InterlockedExchange(&g_hasNewPoint, 1);
                LeaveCriticalSection(&g_cs);

                lastX = ms->pt.x;
                lastY = ms->pt.y;
            }
        }
    }
    return CallNextHookEx(g_mouseHook, nCode, wParam, lParam);
}

// ----------------------------
// Hotkey helpers
// ----------------------------
static void unregister_hotkey(HWND hwnd) {
    UnregisterHotKey(hwnd, HOTKEY_ID_TOGGLE);
}

static void register_hotkey_from_cfg(HWND hwnd) {
    unregister_hotkey(hwnd);
    RegisterHotKey(hwnd, HOTKEY_ID_TOGGLE, g_cfg.hotkey_mods, g_cfg.hotkey_vk);
}

static void set_hotkey_text(HWND edit, UINT mods, UINT vk) {
    wchar_t buf[64] = { 0 };
    int first = 1;

    if (mods & MOD_CONTROL) { StringCchCatW(buf, _countof(buf), L"Ctrl"); first = 0; }
    if (mods & MOD_ALT) { if (!first) StringCchCatW(buf, _countof(buf), L"+"); StringCchCatW(buf, _countof(buf), L"Alt"); first = 0; }
    if (mods & MOD_SHIFT) { if (!first) StringCchCatW(buf, _countof(buf), L"+"); StringCchCatW(buf, _countof(buf), L"Shift"); first = 0; }
    if (mods & MOD_WIN) { if (!first) StringCchCatW(buf, _countof(buf), L"+"); StringCchCatW(buf, _countof(buf), L"Win"); first = 0; }

    if (!first) StringCchCatW(buf, _countof(buf), L"+");

    if ((vk >= 'A' && vk <= 'Z') || (vk >= '0' && vk <= '9')) {
        wchar_t c[2] = { (wchar_t)vk, 0 };
        StringCchCatW(buf, _countof(buf), c);
    }
    else if (vk == VK_SPACE) {
        StringCchCatW(buf, _countof(buf), L"Space");
    }
    else {
        wchar_t tmp[16];
        StringCchPrintfW(tmp, _countof(tmp), L"VK(%u)", vk);
        StringCchCatW(buf, _countof(buf), tmp);
    }

    SetWindowTextW(edit, buf);
}

static UINT current_mods(void) {
    UINT mods = 0;
    if (GetAsyncKeyState(VK_CONTROL) & 0x8000) mods |= MOD_CONTROL;
    if (GetAsyncKeyState(VK_MENU) & 0x8000)    mods |= MOD_ALT;
    if (GetAsyncKeyState(VK_SHIFT) & 0x8000)   mods |= MOD_SHIFT;
    if ((GetAsyncKeyState(VK_LWIN) & 0x8000) || (GetAsyncKeyState(VK_RWIN) & 0x8000)) mods |= MOD_WIN;
    return mods;
}

// ----------------------------
// Tray helpers (W)
// ----------------------------
static void tray_update_tip(void) {
    wchar_t tip[128];
    StringCchPrintfW(tip, _countof(tip), L"%s %s [%s]\r\n速度=%dx",
        APP_NAME, APP_VERSION,
        (InterlockedCompareExchange(&g_active, 0, 0) ? L"ON" : L"OFF"),
        g_cfg.scroll_notches_per_step);
    lstrcpynW(g_nid.szTip, tip, (int)_countof(g_nid.szTip));
    g_nid.uFlags = NIF_TIP;
    Shell_NotifyIconW(NIM_MODIFY, &g_nid);
}

static void tray_set_icon(HICON hIcon) {
    g_nid.uFlags = NIF_ICON;
    g_nid.hIcon = hIcon;
    Shell_NotifyIconW(NIM_MODIFY, &g_nid);
}

static void tray_show_menu(HWND hwnd) {
    POINT pt;
    GetCursorPos(&pt);
    SetForegroundWindow(hwnd);

    ModifyMenuW(g_trayMenu, IDM_TRAY_TOGGLE, MF_BYCOMMAND | MF_STRING, IDM_TRAY_TOGGLE,
        (InterlockedCompareExchange(&g_active, 0, 0) ? L"OFF にする" : L"ON にする"));

    TrackPopupMenu(g_trayMenu, TPM_RIGHTBUTTON, pt.x, pt.y, 0, hwnd, NULL);
    PostMessage(hwnd, WM_NULL, 0, 0);
}

// ----------------------------
// Visuals
// ----------------------------
static void paint_status_box(HWND hwnd, HDC hdc) {
    RECT rc;
    GetClientRect(hwnd, &rc);

    LONG on = InterlockedCompareExchange(&g_active, 0, 0);
    HBRUSH br = CreateSolidBrush(on ? RGB(40, 120, 255) : RGB(220, 50, 50));
    FillRect(hdc, &rc, br);
    DeleteObject(br);

    FrameRect(hdc, &rc, (HBRUSH)GetStockObject(BLACK_BRUSH));
}

static void update_visuals(void) {
    LONG on = InterlockedCompareExchange(&g_active, 0, 0);

    SetWindowTextW(g_statusText, on ? L"有効 (ON)" : L"無効 (OFF)");
    SendMessageW(g_invertCheck, BM_SETCHECK, g_cfg.invert_direction ? BST_CHECKED : BST_UNCHECKED, 0);
    set_hotkey_text(g_hotkeyEdit, g_cfg.hotkey_mods, g_cfg.hotkey_vk);

    if (g_speedText) {
        wchar_t s[32];
        StringCchPrintfW(s, _countof(s), L"%dx", g_cfg.scroll_notches_per_step);
        SetWindowTextW(g_speedText, s);
    }
    if (g_speedSlider) {
        SendMessageW(g_speedSlider, TBM_SETPOS, TRUE, g_cfg.scroll_notches_per_step);
    }

    if (g_startMinCheck) {
        SendMessageW(g_startMinCheck, BM_SETCHECK, g_cfg.start_minimized ? BST_CHECKED : BST_UNCHECKED, 0);
    }
    if (g_startupShortcutCheck) {
        SendMessageW(g_startupShortcutCheck, BM_SETCHECK, g_cfg.startup_shortcut ? BST_CHECKED : BST_UNCHECKED, 0);
    }

    wchar_t title[240];
    StringCchPrintfW(title, _countof(title),
        L"%s %s  [%s]  (開始:%0.0f° / 反応:%0.0f° / 停止:%ums)",
        APP_NAME, APP_VERSION,
        on ? L"ON" : L"OFF",
        ARM_START_DEG, STEP_DEG_ARMED, (unsigned)DISARM_IDLE_MS);
    SetWindowTextW(g_hwnd, title);

    SendMessageW(g_hwnd, WM_SETICON, ICON_SMALL, (LPARAM)(on ? g_iconOn : g_iconOff));
    SendMessageW(g_hwnd, WM_SETICON, ICON_BIG, (LPARAM)(on ? g_iconOn : g_iconOff));

    tray_set_icon(on ? g_iconOn : g_iconOff);
    tray_update_tip();

    InvalidateRect(g_statusBox, NULL, TRUE);
    InvalidateRect(g_hwnd, NULL, TRUE);
}

// ----------------------------
// Apply ON/OFF
// ----------------------------
static void apply_active(int on) {
    InterlockedExchange(&g_active, on ? 1 : 0);
    clear_pending_point();
    reset_gesture_state();

    g_cfg.active = on ? 1 : 0;
    save_config(&g_cfg);

    update_visuals();
}

// ----------------------------
// Usage text (W)
// ----------------------------
static const wchar_t* USAGE_TEXT =
L"■ 使い方（トラックパッド設定）\r\n"
L"1) Windows 11 設定 → Bluetooth とデバイス → タッチパッド\r\n"
L"2) 3本指/4本指ジェスチャーで「キーボードショートカット」を割り当て\r\n"
L"3) このアプリのホットキー（例: Ctrl+Alt+S）を割り当て\r\n\r\n"
L"■ 操作\r\n"
L"- ホットキーで ON/OFF トグル\r\n"
L"- ON の間：円を描くように動かすとスクロール\r\n\r\n"
L"■ 誤反応対策（今回の仕様）\r\n"
L"- 最初の1周（360°）まではスクロールしません（開始は厳しめ）\r\n"
L"- 1周を満たして“開始”した後は、より小さい角度でスクロールします（反応は軽め）\r\n"
L"- 回転が止まると“開始”は解除されます（停止後は再度1周で開始が必要）\r\n"
L"- 直線っぽい動きは無反応（pathLen/chordLen による曲率ゲート）\r\n\r\n"
L"■ 速度\r\n"
L"- 「スクロール速度」はホイール送信量の倍率（1..10）です\r\n"
L"- Windows側の「ホイールで何行スクロールするか」設定も影響します\r\n\r\n"
L"■ スタートアップ\r\n"
L"- 「スタートアップへショートカット作成」をONにして適用すると\r\n"
L"  shell:startup に .lnk を作成します（OFFで削除）\r\n"
L"- 「起動時にGUIを隠す」をONにすると、起動直後にトレイ常駐します\r\n";

// ----------------------------
// Window proc
// ----------------------------
static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {

    case WM_CREATE: {
        HFONT hFont = (HFONT)GetStockObject(DEFAULT_GUI_FONT);

        CreateWindowW(L"STATIC", L"使い方 / 説明",
            WS_CHILD | WS_VISIBLE,
            10, 10, 520, 18,
            hwnd, NULL, NULL, NULL);

        // Usage edit: height 300
        g_usageEdit = CreateWindowExW(WS_EX_CLIENTEDGE, L"EDIT", L"",
            WS_CHILD | WS_VISIBLE | ES_MULTILINE | ES_AUTOVSCROLL | ES_READONLY | WS_VSCROLL,
            10, 30, 520, 300,
            hwnd, (HMENU)IDC_USAGE_EDIT, NULL, NULL);
        SendMessageW(g_usageEdit, WM_SETFONT, (WPARAM)hFont, TRUE);
        SetWindowTextW(g_usageEdit, USAGE_TEXT);

        // below
        const int baseY = 340;

        CreateWindowW(L"STATIC", L"状態",
            WS_CHILD | WS_VISIBLE,
            10, baseY, 60, 18,
            hwnd, NULL, NULL, NULL);

        g_statusBox = CreateWindowW(L"STATIC", L"",
            WS_CHILD | WS_VISIBLE,
            70, baseY - 2, 18, 18,
            hwnd, (HMENU)IDC_STATUS_BOX, NULL, NULL);

        g_statusText = CreateWindowW(L"STATIC", L"",
            WS_CHILD | WS_VISIBLE,
            95, baseY - 2, 220, 18,
            hwnd, (HMENU)IDC_STATUS_TEXT, NULL, NULL);
        SendMessageW(g_statusText, WM_SETFONT, (WPARAM)hFont, TRUE);

        g_toggleBtn = CreateWindowW(L"BUTTON", L"ON/OFF 切替",
            WS_CHILD | WS_VISIBLE,
            360, baseY - 5, 170, 26,
            hwnd, (HMENU)IDC_TOGGLE_BTN, NULL, NULL);
        SendMessageW(g_toggleBtn, WM_SETFONT, (WPARAM)hFont, TRUE);

        g_invertCheck = CreateWindowW(L"BUTTON", L"回転方向を反転（上下を逆にする）",
            WS_CHILD | WS_VISIBLE | BS_AUTOCHECKBOX,
            10, baseY + 30, 340, 22,
            hwnd, (HMENU)IDC_INVERT_CHECK, NULL, NULL);
        SendMessageW(g_invertCheck, WM_SETFONT, (WPARAM)hFont, TRUE);

        CreateWindowW(L"STATIC", L"ホットキー（トグル）",
            WS_CHILD | WS_VISIBLE,
            10, baseY + 60, 200, 18,
            hwnd, NULL, NULL, NULL);

        g_hotkeyEdit = CreateWindowExW(WS_EX_CLIENTEDGE, L"EDIT", L"",
            WS_CHILD | WS_VISIBLE | ES_READONLY,
            10, baseY + 80, 180, 24,
            hwnd, (HMENU)IDC_HOTKEY_EDIT, NULL, NULL);
        SendMessageW(g_hotkeyEdit, WM_SETFONT, (WPARAM)hFont, TRUE);

        g_hotkeySetBtn = CreateWindowW(L"BUTTON", L"変更（押してからキー入力）",
            WS_CHILD | WS_VISIBLE,
            200, baseY + 80, 170, 24,
            hwnd, (HMENU)IDC_HOTKEY_SET_BTN, NULL, NULL);
        SendMessageW(g_hotkeySetBtn, WM_SETFONT, (WPARAM)hFont, TRUE);

        g_applyBtn = CreateWindowW(L"BUTTON", L"設定を適用",
            WS_CHILD | WS_VISIBLE,
            380, baseY + 80, 150, 24,
            hwnd, (HMENU)IDC_APPLY_BTN, NULL, NULL);
        SendMessageW(g_applyBtn, WM_SETFONT, (WPARAM)hFont, TRUE);

        // speed
        CreateWindowW(L"STATIC", L"スクロール速度",
            WS_CHILD | WS_VISIBLE,
            10, baseY + 120, 120, 18,
            hwnd, NULL, NULL, NULL);

        g_speedText = CreateWindowW(L"STATIC", L"",
            WS_CHILD | WS_VISIBLE,
            130, baseY + 120, 60, 18,
            hwnd, (HMENU)IDC_SPEED_TEXT, NULL, NULL);
        SendMessageW(g_speedText, WM_SETFONT, (WPARAM)hFont, TRUE);

        g_speedSlider = CreateWindowExW(0, TRACKBAR_CLASSW, L"",
            WS_CHILD | WS_VISIBLE | TBS_AUTOTICKS,
            10, baseY + 140, 240, 30,
            hwnd, (HMENU)IDC_SPEED_SLIDER, NULL, NULL);

        SendMessageW(g_speedSlider, TBM_SETRANGE, TRUE, MAKELPARAM(1, 10));
        SendMessageW(g_speedSlider, TBM_SETPAGESIZE, 0, 1);
        SendMessageW(g_speedSlider, TBM_SETPOS, TRUE, g_cfg.scroll_notches_per_step);

        // startup options
        g_startMinCheck = CreateWindowW(L"BUTTON", L"起動時にGUIを隠す（トレイ常駐）",
            WS_CHILD | WS_VISIBLE | BS_AUTOCHECKBOX,
            280, baseY + 120, 260, 22,
            hwnd, (HMENU)IDC_STARTMIN_CHECK, NULL, NULL);
        SendMessageW(g_startMinCheck, WM_SETFONT, (WPARAM)hFont, TRUE);

        g_startupShortcutCheck = CreateWindowW(L"BUTTON", L"スタートアップへショートカット作成（OFFで削除）",
            WS_CHILD | WS_VISIBLE | BS_AUTOCHECKBOX,
            280, baseY + 145, 300, 22,
            hwnd, (HMENU)IDC_STARTUPSHORT_CHECK, NULL, NULL);
        SendMessageW(g_startupShortcutCheck, WM_SETFONT, (WPARAM)hFont, TRUE);

        g_minTrayBtn = CreateWindowW(L"BUTTON", L"トレイに最小化",
            WS_CHILD | WS_VISIBLE,
            380, baseY + 180, 150, 24,
            hwnd, (HMENU)IDC_MINIMIZE_TRAY_BTN, NULL, NULL);
        SendMessageW(g_minTrayBtn, WM_SETFONT, (WPARAM)hFont, TRUE);

        update_visuals();
        return 0;
    }

    case WM_COMMAND: {
        switch (LOWORD(wParam)) {
        case IDC_TOGGLE_BTN: {
            LONG cur = InterlockedCompareExchange(&g_active, 0, 0);
            apply_active(cur ? 0 : 1);
            return 0;
        }
        case IDC_INVERT_CHECK: {
            g_cfg.invert_direction =
                (SendMessageW(g_invertCheck, BM_GETCHECK, 0, 0) == BST_CHECKED) ? 1 : 0;
            save_config(&g_cfg);
            update_visuals();
            return 0;
        }
        case IDC_HOTKEY_SET_BTN: {
            g_capturingHotkey = 1;
            SetWindowTextW(g_hotkeySetBtn, L"入力待ち…（Escで取消）");
            SetFocus(hwnd);
            return 0;
        }
        case IDC_APPLY_BTN: {
            g_cfg.invert_direction =
                (SendMessageW(g_invertCheck, BM_GETCHECK, 0, 0) == BST_CHECKED) ? 1 : 0;

            g_cfg.start_minimized =
                (SendMessageW(g_startMinCheck, BM_GETCHECK, 0, 0) == BST_CHECKED) ? 1 : 0;

            g_cfg.startup_shortcut =
                (SendMessageW(g_startupShortcutCheck, BM_GETCHECK, 0, 0) == BST_CHECKED) ? 1 : 0;

            if (!ensure_startup_shortcut(g_cfg.startup_shortcut)) {
                MessageBoxW(hwnd,
                    L"スタートアップショートカットの操作に失敗しました。\r\n"
                    L"（権限または環境により作成できない場合があります）",
                    APP_NAME, MB_ICONWARNING);
            }

            save_config(&g_cfg);
            register_hotkey_from_cfg(hwnd);
            update_visuals();
            MessageBeep(MB_OK);
            return 0;
        }
        case IDC_MINIMIZE_TRAY_BTN: {
            ShowWindow(hwnd, SW_HIDE);
            return 0;
        }
        case IDM_TRAY_TOGGLE: {
            LONG cur = InterlockedCompareExchange(&g_active, 0, 0);
            apply_active(cur ? 0 : 1);
            return 0;
        }
        case IDM_TRAY_SHOW: {
            ShowWindow(hwnd, SW_SHOW);
            ShowWindow(hwnd, SW_RESTORE);
            SetForegroundWindow(hwnd);
            InvalidateRect(hwnd, NULL, TRUE);
            return 0;
        }
        case IDM_TRAY_EXIT: {
            PostMessage(hwnd, WM_CLOSE, 0, 0);
            return 0;
        }
        }
        break;
    }

    case WM_HSCROLL:
        if ((HWND)lParam == g_speedSlider) {
            int pos = (int)SendMessageW(g_speedSlider, TBM_GETPOS, 0, 0);
            if (pos < 1) pos = 1;
            if (pos > 10) pos = 10;
            g_cfg.scroll_notches_per_step = pos;
            save_config(&g_cfg);
            update_visuals();
            return 0;
        }
        break;

    case WM_KEYDOWN:
        if (g_capturingHotkey) {
            if (wParam == VK_ESCAPE) {
                g_capturingHotkey = 0;
                SetWindowTextW(g_hotkeySetBtn, L"変更（押してからキー入力）");
                update_visuals();
                return 0;
            }

            UINT vk = (UINT)wParam;

            // reject pure modifier keys
            if (vk == VK_CONTROL || vk == VK_SHIFT || vk == VK_MENU || vk == VK_LWIN || vk == VK_RWIN ||
                vk == VK_LCONTROL || vk == VK_RCONTROL || vk == VK_LSHIFT || vk == VK_RSHIFT ||
                vk == VK_LMENU || vk == VK_RMENU) {
                return 0;
            }

            UINT mods = current_mods();
            if (mods == 0) {
                MessageBeep(MB_ICONWARNING);
                return 0;
            }

            g_cfg.hotkey_mods = mods;
            g_cfg.hotkey_vk = vk;

            g_capturingHotkey = 0;
            SetWindowTextW(g_hotkeySetBtn, L"変更（押してからキー入力）");
            set_hotkey_text(g_hotkeyEdit, g_cfg.hotkey_mods, g_cfg.hotkey_vk);
            save_config(&g_cfg);
            MessageBeep(MB_OK);
            return 0;
        }
        break;

    case WM_HOTKEY:
        if (wParam == HOTKEY_ID_TOGGLE) {
            LONG cur = InterlockedCompareExchange(&g_active, 0, 0);
            apply_active(cur ? 0 : 1);
            return 0;
        }
        break;

    case WM_TRAYICON:
        if (lParam == WM_RBUTTONUP) {
            tray_show_menu(hwnd);
            return 0;
        }
        else if (lParam == WM_LBUTTONDBLCLK) {
            ShowWindow(hwnd, SW_SHOW);
            ShowWindow(hwnd, SW_RESTORE);
            SetForegroundWindow(hwnd);
            InvalidateRect(hwnd, NULL, TRUE);
            return 0;
        }
        break;

        // Theme-aligned background
    case WM_CTLCOLORSTATIC:
    case WM_CTLCOLOREDIT: {
        HDC hdc = (HDC)wParam;
        SetBkMode(hdc, TRANSPARENT);
        SetTextColor(hdc, GetSysColor(COLOR_WINDOWTEXT));
        return (LRESULT)GetSysColorBrush(COLOR_WINDOW);
    }

    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC hdc = BeginPaint(hwnd, &ps);

        RECT rc;
        GetClientRect(hwnd, &rc);
        FillRect(hdc, &rc, GetSysColorBrush(COLOR_WINDOW));

        if (g_statusBox) {
            HDC hdcBox = GetDC(g_statusBox);
            paint_status_box(g_statusBox, hdcBox);
            ReleaseDC(g_statusBox, hdcBox);
        }

        EndPaint(hwnd, &ps);
        return 0;
    }

    case WM_CLOSE:
        DestroyWindow(hwnd);
        return 0;

    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }

    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

// ----------------------------
// WinMain (W)
// ----------------------------
int WINAPI wWinMain(HINSTANCE hInst, HINSTANCE hPrev, PWSTR lpCmd, int nShow) {
    (void)hPrev; (void)lpCmd; (void)nShow;

    CoInitializeEx(NULL, COINIT_APARTMENTTHREADED);

    INITCOMMONCONTROLSEX icc;
    icc.dwSize = sizeof(icc);
    icc.dwICC = ICC_BAR_CLASSES;
    InitCommonControlsEx(&icc);

    load_config(&g_cfg);

    // reconcile startup shortcut based on INI (best-effort)
    ensure_startup_shortcut(g_cfg.startup_shortcut);

    InterlockedExchange(&g_active, g_cfg.active ? 1 : 0);

    InitializeCriticalSection(&g_cs);

    g_iconOn = create_solid_icon(RGB(40, 120, 255));
    g_iconOff = create_solid_icon(RGB(220, 50, 50));

    WNDCLASSW wc;
    ZeroMemory(&wc, sizeof(wc));
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.lpszClassName = WIN_CLASS;
    wc.hCursor = LoadCursorW(NULL, IDC_ARROW);
    wc.hIcon = g_iconOff ? g_iconOff : LoadIconW(NULL, IDI_APPLICATION);
    wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);

    if (!RegisterClassW(&wc)) {
        MessageBoxW(NULL, L"RegisterClass failed.", APP_NAME, MB_ICONERROR);
        CoUninitialize();
        return 1;
    }

    // Window size for usage height 300
    g_hwnd = CreateWindowExW(0, WIN_CLASS, APP_NAME,
        WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX,
        CW_USEDEFAULT, CW_USEDEFAULT, 600, 650,
        NULL, NULL, hInst, NULL);

    if (!g_hwnd) {
        MessageBoxW(NULL, L"CreateWindow failed.", APP_NAME, MB_ICONERROR);
        CoUninitialize();
        return 1;
    }

    SendMessageW(g_hwnd, WM_SETICON, ICON_SMALL, (LPARAM)(g_cfg.active ? g_iconOn : g_iconOff));
    SendMessageW(g_hwnd, WM_SETICON, ICON_BIG, (LPARAM)(g_cfg.active ? g_iconOn : g_iconOff));

    g_mouseHook = SetWindowsHookExW(WH_MOUSE_LL, LowLevelMouseProc, hInst, 0);
    if (!g_mouseHook) {
        MessageBoxW(NULL, L"SetWindowsHookEx(WH_MOUSE_LL) failed.", APP_NAME, MB_ICONERROR);
        CoUninitialize();
        return 1;
    }

    g_workerThread = (HANDLE)_beginthreadex(NULL, 0, WorkerThread, NULL, 0, NULL);
    if (!g_workerThread) {
        MessageBoxW(NULL, L"Worker thread create failed.", APP_NAME, MB_ICONERROR);
        CoUninitialize();
        return 1;
    }

    ZeroMemory(&g_nid, sizeof(g_nid));
    g_nid.cbSize = sizeof(g_nid);
    g_nid.hWnd = g_hwnd;
    g_nid.uID = 1;
    g_nid.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP;
    g_nid.uCallbackMessage = WM_TRAYICON;
    g_nid.hIcon = g_cfg.active ? g_iconOn : g_iconOff;
    lstrcpynW(g_nid.szTip, L"GestureScroll", (int)_countof(g_nid.szTip));
    Shell_NotifyIconW(NIM_ADD, &g_nid);
    tray_update_tip();

    g_trayMenu = CreatePopupMenu();
    AppendMenuW(g_trayMenu, MF_STRING, IDM_TRAY_TOGGLE, L"ON/OFF 切替");
    AppendMenuW(g_trayMenu, MF_STRING, IDM_TRAY_SHOW, L"表示");
    AppendMenuW(g_trayMenu, MF_SEPARATOR, 0, NULL);
    AppendMenuW(g_trayMenu, MF_STRING, IDM_TRAY_EXIT, L"終了");

    register_hotkey_from_cfg(g_hwnd);

    ShowWindow(g_hwnd, SW_SHOW);
    UpdateWindow(g_hwnd);
    update_visuals();

    if (g_cfg.start_minimized) {
        ShowWindow(g_hwnd, SW_HIDE);
    }

    MSG msg;
    while (GetMessageW(&msg, NULL, 0, 0) > 0) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    unregister_hotkey(g_hwnd);

    Shell_NotifyIconW(NIM_DELETE, &g_nid);
    if (g_trayMenu) { DestroyMenu(g_trayMenu); g_trayMenu = NULL; }

    if (g_mouseHook) { UnhookWindowsHookEx(g_mouseHook); g_mouseHook = NULL; }

    InterlockedExchange(&g_running, 0);
    if (g_workerThread) {
        WaitForSingleObject(g_workerThread, INFINITE);
        CloseHandle(g_workerThread);
        g_workerThread = NULL;
    }

    DeleteCriticalSection(&g_cs);

    if (g_iconOn) DestroyIcon(g_iconOn);
    if (g_iconOff) DestroyIcon(g_iconOff);

    CoUninitialize();
    return 0;
}
