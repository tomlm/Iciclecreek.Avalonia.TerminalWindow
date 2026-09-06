using Avalonia;
using Avalonia.Controls;
using Avalonia.Input;
using Avalonia.Input.Platform;
using Avalonia.Input.TextInput;
using Avalonia.Interactivity;
using Avalonia.LogicalTree;
using Avalonia.Media;
using Avalonia.Media.TextFormatting;
using Avalonia.Media.Immutable;
using Avalonia.Media.Imaging;
using Avalonia.Platform;
using Avalonia.Rendering;
using Avalonia.Threading;
using Iciclecreek.Avalonia.Terminal;
using Porta.Pty;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using XTerm.Buffer;
using XTerm.Events;
using XT = global::XTerm;

namespace Iciclecreek.Terminal
{

    public partial class TerminalView : Control, ICustomHitTest, IDisposable
    {
        /// <summary>
        /// Avalonia hit-tests what a control actually DREW, not the rectangle it occupies — the same
        /// rule that makes a <c>Grid</c> with no Background invisible to the pointer. <see cref="Render"/> paints
        /// glyph runs and per-cell background fills, and the fills are skipped for cells carrying no background of
        /// their own, so a terminal is hit-testable only over the pixels that happen to have text on them. The
        /// pointer landed on whatever sat BEHIND the view everywhere else: wheel events over blank space, over the
        /// gap right of a short line, or below the last line never reached the terminal at all, which reads as a
        /// terminal that only sometimes agrees to scroll. The whole rect is an input surface — click-to-focus,
        /// selection drags and the wheel all depend on it.
        /// </summary>
        public bool HitTest(Point point) => new Rect(Bounds.Size).Contains(point);

        private XT.Terminal _terminal;

        private readonly Skia.SnapshotBuilder _snapshotBuilder = new();
        private readonly Skia.SkiaFontCache _skiaFonts = new();

        /// <summary>
        /// Whether the cell grid is drawn straight onto the Skia canvas instead of through
        /// DrawingContext. Off by default — the classic path is untouched until a host opts in.
        /// See the notes on TerminalSkiaLayer for what the direct path gives up.
        /// </summary>
        public static readonly StyledProperty<bool> UseSkiaRendererProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(UseSkiaRenderer),
                defaultValue: false);

        /// <summary>Whether the cell grid is drawn straight onto the Skia canvas. See <see cref="UseSkiaRendererProperty"/>.</summary>
        public bool UseSkiaRenderer
        {
            get => GetValue(UseSkiaRendererProperty);
            set => SetValue(UseSkiaRendererProperty, value);
        }

        /// <summary>Latched once a layer reports the backend will not lease a Skia canvas.</summary>
        private bool _skiaUnsupported;

        /// <summary>The layer enqueued last frame, asked afterwards whether it could draw.</summary>
        private Skia.TerminalSkiaLayer? _lastSkiaLayer;


        private FormattedText _measureText;
        private string? _currentDirectory;
        private double _charWidth;
        private double _charHeight;

        /// <summary>
        /// The font chain as one comma-separated string, for the Skia layer, which takes a string
        /// rather than a <see cref="FontFamily"/>. Rebuilt with the metrics it has to agree with.
        /// </summary>
        private string _fontFamilyChain = "monospace";
        private int _bufferSize = 1000;
        private bool _isAlternateBuffer;

        // URL hover state.
        // The pattern is deliberately permissive about trailing characters — `,` `;` `)` and friends are
        // legal inside a url but usually sentence punctuation at the end — so TrimUrlEnd() decides where
        // the url really stops.
        private static readonly Regex UrlRegex = new(@"https?://[^\s<>""'`]+", RegexOptions.Compiled);
        private static readonly Cursor HandCursor = new Cursor(StandardCursorType.Hand);
        private HoveredUrl? _hoveredLink;
        private Cursor? _savedCursor;
        private bool _cursorOverridden;
        private (int Line, int Col)? _lastHoverProbe;
        private HoveredUrl? _pendingUrlClick;

        // Pointer-shape (OSC 22) override state, kept apart from the hover pair above because the two
        // nest: a shape can arrive during a hover and a hover can start over a shape. This is what the
        // CONTROL's cursor was before the program's first shape took effect, so a reset can put it back
        // — SetCurrentValue overwrites the local value, so without the snapshot an embedder who wrote
        // <TerminalView Cursor="IBeam"/> lost it the first time a program reset the shape.
        private Cursor? _preShapeCursor;
        private bool _shapeOverridden;

        // Process management
        private IPtyConnection? _ptyConnection;

        /// <summary>
        /// True while an application has declared an atomic update — DEC private mode 2026.
        /// </summary>
        /// <remarks>
        /// A full-screen program redraws in many writes. Painting between them shows a frame half old
        /// and half new, which is the tearing you see when a TUI repaints under load. While this is
        /// set the view stops asking for frames, so the last complete one stays on screen, and the end
        /// of the update asks for exactly one.
        /// <para>Volatile because the two sides are different threads: it is set and cleared on the PTY
        /// reader thread, and read on the UI thread as well — the cursor blink, the animation clock, and
        /// every mouse, key and selection path reach <c>RequestPaint</c>. The volatile write is what
        /// publishes <see cref="_atomicUpdateStartedAt"/> along with it; see <see cref="BeginAtomicUpdate"/>
        /// for what a reader that saw the flag without the timestamp would do.</para>
        /// </remarks>
        private volatile bool _atomicUpdate;

        /// <summary>Complete frames of the viewport, published by the reader for the renderer.</summary>
        /// <remarks>See <see cref="FrameCapturePool"/> for the tearing this exists to stop.</remarks>
        private readonly FrameCapturePool _frameCapture = new();

        /// <summary>
        /// Counts every write this view delivers into the emulator's buffer.
        /// </summary>
        /// <remarks>
        /// The freshness key for a captured frame: a capture taken at generation G is exact while
        /// the generation is still G, because nothing has written the buffer since. Bumped BEFORE
        /// each write, so a capture published from inside that write — the ESU handler runs inside
        /// <c>Terminal.Write</c> — records the generation the buffer will be at when the write
        /// completes, and is current from the moment it exists.
        /// </remarks>
        private long _liveWriteGeneration;
        /// <summary>When the open atomic update began, as a Stopwatch timestamp.</summary>
        /// <remarks>
        /// Written beside <see cref="_atomicUpdate"/> on the reader thread and read wherever the
        /// deadline is tested. Only meaningful while that flag is set, and always written BEFORE
        /// it: the flag is volatile, so writing it releases this one, and a reader that sees the
        /// flag set sees the timestamp that belongs to it. Plain rather than volatile itself for
        /// exactly that reason — the flag publishes it, and it is never read except after the flag
        /// has been found set.
        /// </remarks>
        private long _atomicUpdateStartedAt;

        /// <summary>
        /// Whether the pty reader is inside <c>Terminal.Write</c> right now.
        /// </summary>
        /// <remarks>
        /// The renderer's capture gate needs it: DEC 2026 only declares the buffer mid-frame from
        /// the BSU byte onward, but the buffer is just as mid-write while the bytes BEFORE the BSU
        /// of a chunk are parsing — and a paint in that window used to fall back to the live
        /// buffer and tear. Raised and lowered on the reader thread around the write; volatile so
        /// the UI thread reads the current value rather than a cached one. A false read racing the
        /// flag going up narrows the exposure from the length of a chunk parse to the length of a
        /// field write, which is the practical difference between one torn paint in twenty and
        /// none observed.
        /// </remarks>
        private volatile bool _bufferWriteInProgress;

        /// <summary>
        /// How long a hold may last before the view paints anyway.
        /// </summary>
        /// <remarks>
        /// Not optional. An application that begins an update and then crashes, or is stopped at a
        /// breakpoint, would otherwise freeze the display for as long as it stays that way — the one
        /// failure mode of this feature, and worse than the tearing it prevents. A tear is a bad
        /// frame; a permanently frozen terminal looks like the application hung.
        /// </remarks>
        private static readonly TimeSpan AtomicUpdateTimeout = TimeSpan.FromMilliseconds(150);
        private CancellationTokenSource? _processCts;
        private static readonly Encoding Utf8NoBom = new UTF8Encoding(encoderShouldEmitUTF8Identifier: false);
        private int _processExitHandled;    // 0=false, 1=true — claimed via TryClaimExit

        /// <summary>
        /// Guards the PAIR (<see cref="_ptyConnection"/>, <see cref="_processExitHandled"/>). They have to move
        /// together, or a read loop belonging to a DEAD connection can report an exit against a LIVE one.
        ///
        /// <para>The loop's ownership test is its <c>while</c> condition, evaluated BEFORE the read. A relaunch
        /// can replace the connection while that read is pending — and Porta.Pty's Unix reader wraps a
        /// synchronous FileStream, so cancellation does not reliably interrupt it. When the old stream is closed
        /// the read completes, and the stale loop walks into the exit path holding a connection nobody owns any
        /// more. Because the relaunch also reset the flag for the new process, its claim SUCCEEDS: the freshly
        /// started terminal immediately prints the previous process's exit code.</para>
        /// </summary>
        private readonly object _exitGate = new object();

        /// <summary>Ceiling on waiting for an already-exited child to be reaped so its real exit
        /// code is readable. See the EOF branch of <see cref="ReadPtyOutputAsync"/>.</summary>
        private const int ExitReapGraceMs = 1000;

        /// <summary>How long the BACKGROUND wait keeps trying after the read loop's grace period expires.
        /// The child is dead by definition, so this is a ceiling on patience, not an expected cost.</summary>
        private const int ExitReapCeilingMs = 30_000;

        /// <summary>Poll slice for that wait. Short enough to report promptly, long enough not to spin.</summary>
        private const int ExitReapPollMs = 100;
        private readonly object _terminalLock = new object(); // Serialises all _terminal.Write/WriteLine calls

        // Cursor blinking
        private DispatcherTimer _cursorBlinkTimer;
        private bool _cursorBlinkOn = true;

        /// <summary>
        /// Set while ArrangeOverride is re-gridding the emulator to match the size the host already
        /// gave this control, so <see cref="OnTerminalResized"/> can tell that resize from the ones a
        /// program asks for with DECCOLM.
        /// </summary>
        private bool _regridFromLayout;

        /// <summary>
        /// The DEC status line's single row, or <see langword="null"/> when there is no status line.
        /// </summary>
        /// <remarks>
        /// <para>A <c>BufferLine</c> because that is what it is -- one row with per-cell attributes,
        /// which vttest writes graphic renditions into. The emulator owns it (XTerm.NET#148, the
        /// state half of the split); <see cref="OnTerminalStatusLineChanged"/> hands it in through
        /// <see cref="SetStatusLine"/>, which the tests also drive directly.</para>
        /// <para>Held rather than read through on demand for the reason every other frame input is
        /// snapshotted: the row is drawn from the UI thread while the pty thread may be writing it.</para>
        /// </remarks>
        private XT.Buffer.BufferLine? _statusLine;

        /// <summary>
        /// The height the status line takes out of this control, in pixels: one row, or nothing.
        /// </summary>
        /// <remarks>
        /// Taken off the height BEFORE the grid is counted, so the row is not one of the terminal's
        /// rows. That is what keeps <c>CSI 18 t</c>, the pixel-geometry reports and the pty size
        /// honest without any of them knowing this exists -- every one of them is computed from
        /// <c>_terminal.Rows</c>, and the status row was never in it.
        /// </remarks>
        private double StatusLineHeight => _statusLine is null ? 0 : _charHeight;

        /// <summary>
        /// Sets the row drawn as the DEC status line, or clears it with <see langword="null"/>.
        /// </summary>
        /// <remarks>
        /// <para>The seam between the emulator's state and this view's pixels:
        /// <see cref="OnTerminalStatusLineChanged"/> calls it with the emulator's row (or null),
        /// and the tests call it directly -- which is how the drawing and the geometry were
        /// written and pinned before the emulator half existed.</para>
        /// <para>Appearing or disappearing changes how many rows fit, so this re-runs layout rather
        /// than only repainting: the grid is a row shorter while a status line is shown. Setting the
        /// same presence again is only a repaint, because the row's CONTENT changing does not move
        /// anything.</para>
        /// </remarks>
        internal void SetStatusLine(XT.Buffer.BufferLine? line)
        {
            var appearedOrVanished = (_statusLine is null) != (line is null);
            _statusLine = line;

            if (appearedOrVanished)
            {
                InvalidateMeasure();
                InvalidateArrange();
            }

            InvalidateVisual();
        }

        // Selection state - tracks whether terminal is handling selection vs forwarding mouse to app
        private bool _isSelecting = false;
        // When non-null, a single left-click has been pressed but the selection hasn't started yet.
        // Selection start is deferred until pointer movement so that a plain click doesn't show a caret.
        private (int Col, int Row)? _pendingSelectionStart = null;

        /// <summary>The last motion reported to the application, so an unchanged one is not re-sent.</summary>
        private (int Col, int Row, XT.Input.MouseEventType Type, XT.Input.MouseTrackingMode Mode,
                 XT.Input.MouseButton Button, XT.Input.KeyModifiers Modifiers)? _lastReportedMotion;

        // Wheel accumulator. A notched mouse delivers Delta.Y = ±1 per detent, but a trackpad (and any
        // precision mouse) delivers a stream of FRACTIONS — on macOS a slow two-finger drag is dozens of
        // ~0.05 events. Truncating each event to an int on its own rounds every one of those to zero
        // lines, so carry the remainder across events instead.
        private double _wheelResidual;      // local scrollback path
        private double _wheelResidualApp;   // mouse-reporting path (alt-buffer apps: less, vim, htop)

        // True while the view sits at the tail, which is the only state in which new output should drag
        // the viewport along. Sampled from the buffer before each write — see AutoScrollToBottomProperty.
        private bool _followBottom = true;

        // The buffer OnBufferTrimmed is subscribed to, held so the unsubscribe can name the same instance
        // the subscribe used. Terminal.Buffer returns the ACTIVE buffer and swaps to the alternate one while
        // a full-screen app runs, so `_terminal.Buffer.Trimmed -= ...` at an arbitrary moment can detach the
        // handler from a buffer that never had it and leave the real one subscribed.
        private TerminalBuffer? _scrollbackBuffer;

        // AutoScrollToBottom mirrored for the reader thread. The write path runs OFF the UI thread (the
        // Dispatcher.UIThread.Post beside it is the giveaway), so reading the StyledProperty there would be
        // a cross-thread GetValue. Kept in step by OnPropertyChanged.
        private volatile bool _autoScroll = true;

        // Keyboard selection. Both are CARET BOUNDARY ordinals — `row * Cols + col` counting the gaps
        // between cells, not the cells themselves — so Shift+Right from a fresh cursor selects exactly one
        // cell instead of two. Null anchor = no keyboard selection in flight.
        private int? _kbSelAnchor;

        // True while the selection covers the WHOLE input, from a select-all rather than from a gesture the
        // user steered. The caret is then hidden: with everything selected there is no one place it belongs,
        // and every editor that can select all hides it rather than parking it at an arbitrary end.
        private bool _kbSelWholeInput;

        // Where the shell's editable input begins, as an absolute row and a column on it. A keyboard
        // selection stops here rather than running back over the prompt.
        //
        // Derived rather than known: nothing tells a terminal where a prompt ends unless the shell emits
        // semantic markers, which most shells do not by default. What is reliable is the moment the user
        // FIRST types on a row the shell has just moved to — wherever the cursor is then is the end of
        // whatever the shell drew, which is the prompt.
        //
        // Sampled at that keystroke rather than after the write, because a prompt does not arrive whole: on
        // a real bash the newline and the prompt text land in separate reads, so the cursor is still at
        // column 0 when the row changes. Measured — it recorded (row 4, col 0) instead of (row 4, col 10).
        private int _inputStartRow = -1;
        private int _inputStartCol;
        private int _lastOutputRow = -1;

        // True once the shell has told us where its input begins, via OSC 133. A shell that reports it is
        // authoritative, so the guesswork below is switched off for good rather than left to fight it.
        private bool _semanticPrompt;
        // Armed only by shell OUTPUT moving to a new row. Starting armed would let the first interaction
        // record the input start wherever the cursor happens to be — which, if the user has already typed,
        // is the end of their input rather than the start of it, pinning the selection to a stop.
        private bool _inputStartPending;

        internal (int Row, int Col) InputStart => (_inputStartRow, _inputStartCol);

        // Set where a selection is retired by a keystroke that will type, and consumed by whichever path
        // then sends that character — within the same handler invocation, so it never spans two keystrokes.
        private string _pendingReplaceKeys = string.Empty;
        private int _kbSelFocus;

        // IME (Input Method Editor) support
        private TerminalInputMethodClient? _inputMethodClient;

        /// <summary>
        /// The least time between two output-driven IME notifications.
        /// </summary>
        /// <remarks>
        /// Ten a second. Each one reaches IMM32 on the UI thread, which is expensive enough that a
        /// full-screen application redrawing at fifty frames a second could wedge the window with
        /// nothing else going on. Nothing a person does with an input method needs finer than this
        /// -- the rectangle only has to be right by the time they start composing.
        /// </remarks>
        private static readonly TimeSpan ImeNotifyInterval = TimeSpan.FromMilliseconds(100);

        /// <summary>Whether this view holds keyboard focus, readable off the UI thread.</summary>
        /// <remarks>
        /// A plain field rather than the IsFocused property, because the pty reader thread is what
        /// asks and an Avalonia property is not its to read. Volatile is enough: it is written on
        /// the UI thread when focus changes and read on the reader thread, and a reader that sees
        /// the previous value for a moment either sends one notification it need not have or skips
        /// one it could have sent, neither of which matters at a focus change.
        /// </remarks>
        private volatile bool _imeFocused;

        // When the last output-driven IME notification was queued, as a Stopwatch timestamp.
        // Interlocked because the pty reader thread writes it and reads it.
        private long _imeNotifiedAt;

        // 1 while an IME notification is already queued on the dispatcher and has not run yet.
        // Read and written from the pty reader thread and the UI thread, hence Interlocked; see
        // NotifyInputMethodCoalesced for why one notification in flight is enough.
        private int _imeNotifyQueued;

        // The same latch for the animation-clock sync, which ConsumeOutputChunk posts on the same
        // once-per-chunk footing.
        private int _animationSyncQueued;

        // Unique identifier for this terminal instance (for debugging)
        private readonly Guid _instanceId = Guid.NewGuid();

        // When true, OnDetachedFromLogicalTree skips CleanupProcess so the PTY
        // survives a visual-tree re-parent (e.g. floating window pop-out/dock-back).
        private bool _suppressCleanupOnDetach;

        // Background is null for a run that keeps the terminal's own default background — nothing is
        // painted for it, so a host that layers the view over its own themed surface still shows through.
        //
        // Image is non-null for a run of cells showing pieces of a Sixel picture, in which case Text is null and
        // CellCount is how many tiles the run covers. Both kinds live in the same cached list because the cache
        // is replayed verbatim: a picture that was not in it would simply not be drawn on any frame the row was
        // served from cache, which is most of them.
        // Internal rather than private so the runs a frame decided on can be asserted directly. The headless
        // platform's recording DrawingContext throws NotImplementedException from DrawImage, so a rendered frame
        // cannot be inspected for pictures the way it can for text and fills — the cached run list is the last
        // point at which what will be drawn is still observable.
        internal sealed record CachedTextRun(
            FormattedText? Text,
            int StartX,
            int CellCount,
            IBrush? Background,
            XT.Graphics.LinePlacement? Placement = null,
            XT.Graphics.TerminalImage? Image = null,
            XT.Common.UnderlineStyle UnderlineStyle = XT.Common.UnderlineStyle.None,
            IBrush? UnderlineBrush = null,
            GlyphRun? Glyphs = null,
            IBrush? Foreground = null)
        {
            /// <summary>Whether this run draws a picture rather than text.</summary>
            public bool IsImage => Placement is not null && Image is not null;

            /// <summary>
            /// The curly underline's geometry, built on first draw and replayed with the run.
            /// Relative to the run's own origin, so the same geometry is valid at any row --
            /// which is what lets it live in the cache while the line scrolls.
            /// </summary>
            public Geometry? UnderlineGeometry { get; set; }

            /// <summary>
            /// The underline's pen, immutable, with the dash pattern's phase-lock baked into its
            /// offset. Built once for the same reason as the geometry.
            /// </summary>
            public IPen? UnderlinePen { get; set; }
        }

        // One bitmap per image, built on first sight and reused for the life of the picture.
        //
        // There is no dirty-rect culling — Render walks every visible row on every frame — so a picture on screen
        // is re-blitted up to thirty times a second and must never be re-uploaded to do it. Keyed weakly on the
        // image so the bitmap dies when the emulator drops its last cell: no eviction list, and nothing to keep
        // in step with a buffer that scrolls.
        //
        // Wrapped rather than stored bare so a failed upload can be remembered as well as a successful one --
        // otherwise a picture the platform cannot take would be retried on every frame it is on screen.
        private sealed class CachedBitmap
        {
            public Bitmap? Bitmap;

            /// <summary>
            /// Which frame of the picture this bitmap holds.
            /// </summary>
            /// <remarks>
            /// The cache is keyed on the image, which for an animation is not enough on its own --
            /// the pixels move while the key stays the same. The emulator changes this number
            /// whenever they do. A still picture leaves it at zero forever.
            /// </remarks>
            public int FrameSerial;
        }

        private readonly System.Runtime.CompilerServices.ConditionalWeakTable<XT.Graphics.TerminalImage, CachedBitmap> _imageBitmaps = new();

        // Set once if the PLATFORM cannot draw bitmaps at all. Consolonia runs this same control over a
        // text-cell backend where DrawImage means nothing; the terminal should still render its text there
        // rather than throwing out of Render on every frame.
        //
        // Only the exceptions that say so set this — see IndicatesNoRasterBackend. A picture that fails for
        // its own reasons is remembered against that picture instead, because turning every image off for
        // the life of the control on the strength of one bad bitmap would hide the thing that caused it.
        private bool _imageRenderingUnavailable;

        // The colours the frame currently being drawn resolves against. Taken once at the top of Render, so
        // every cell in a frame agrees even if a program repaints the palette midway through.
        //
        // Not nullable: it is seeded alongside the emulator in OnInitialized and replaced at the top of every
        // frame, so no drawing code can reach it unset. Declaring it nullable only pushed the question onto
        // the several call sites that pass it to a non-null parameter, none of which could answer it either.
        private XT.Common.ColorSnapshot _palette;

        /// <summary>
        /// One builder for every text run the renderer collects, reused rather than reallocated.
        /// </summary>
        /// <remarks>
        /// Safe to share because run collection is synchronous, single-pass and entirely on the UI
        /// thread: a run is built and turned into a string before the next one starts, so no two
        /// uses overlap. Held on the instance rather than statically so two views do not contend.
        /// </remarks>
        private readonly StringBuilder _runTextBuilder = new(256);

        /// <summary>
        /// Whether runs may be drawn as pre-shaped glyphs rather than through FormattedText.
        /// </summary>
        /// <remarks>
        /// Exists so the two pipelines can be rendered and COMPARED, which is the only way to see a
        /// difference the test suite cannot: every assertion there is about buffer state or geometry,
        /// and a run drawn wrongly passes all of them. Not a supported switch -- it is here to be
        /// turned off by the bench and by anyone bisecting a rendering complaint.
        /// </remarks>
        internal static bool GlyphRunFastPathEnabled = true;

        /// <summary>The top level this view is in, remembered rather than searched for.</summary>
        private TopLevel? _topLevel;

        /// <summary>
        /// The device scale to snap geometry to.
        /// </summary>
        /// <remarks>
        /// TopLevel.GetTopLevel walks UP the visual tree looking for the root, and this is read once
        /// per frame at the top of Render -- so every frame paid a tree walk to learn something that
        /// changes when the window moves to another display and at no other time. The reference is
        /// captured when the view is attached and dropped when it is detached; the scaling is read
        /// through it each time, since that genuinely can change while attached.
        /// </remarks>
        private double RenderScale => (_topLevel ??= TopLevel.GetTopLevel(this))?.RenderScaling ?? 1.0;

        /// <summary>Distance from a run's top edge to its baseline, at the current font.</summary>
        private double _baseline;

        /// <summary>Glyph typefaces by style and weight, so the font manager is asked once each.</summary>
        private readonly Dictionary<(FontStyle Style, FontWeight Weight), GlyphTypeface?> _glyphTypefaces = new();

        /// <summary>
        /// The emulator's <c>DrawBoldTextInBrightColors</c>, snapshotted per frame beside the palette.
        /// </summary>
        /// <remarks>
        /// A RENDERER option that XTerm.NET carries and cannot act on -- it has no renderer -- so this
        /// host is the only place it can mean anything, and until now it meant nothing here either.
        /// True is both the emulator's default and xterm.js's.
        /// </remarks>
        private bool _boldIsBright = true;

        // The MinimumContrastRatio enforcer, with its (fg, bg) -> adjusted cache. The option is
        // snapshotted into it once per frame beside _boldIsBright; at the default ratio of 1 the
        // per-run call below short-circuits and rendering is byte-identical to before it existed.
        private readonly MinimumContrast _minimumContrast = new();

        public static readonly DirectProperty<TerminalView, bool> IsAlternateBufferProperty =
            AvaloniaProperty.RegisterDirect<TerminalView, bool>(
                nameof(IsAlternateBuffer),
                o => o.IsAlternateBuffer);

        public static readonly DirectProperty<TerminalView, int> BufferSizeProperty =
            AvaloniaProperty.RegisterDirect<TerminalView, int>(
                nameof(BufferSize),
                o => o._bufferSize,
                (o, v) => o._bufferSize = v);

        public static readonly DirectProperty<TerminalView, int> ViewportYProperty =
            AvaloniaProperty.RegisterDirect<TerminalView, int>(
                nameof(ViewportY),
                o => o.ViewportY,
                (o, v) => o.ViewportY = v);

        public static readonly DirectProperty<TerminalView, int> MaxScrollbackProperty =
            AvaloniaProperty.RegisterDirect<TerminalView, int>(
                nameof(MaxScrollback),
                o => o.MaxScrollback);

        public static readonly DirectProperty<TerminalView, int> ViewportLinesProperty =
            AvaloniaProperty.RegisterDirect<TerminalView, int>(
                nameof(ViewportLines),
                o => o.ViewportLines);

        public static readonly DirectProperty<TerminalView, string?> CurrentDirectoryProperty =
            AvaloniaProperty.RegisterDirect<TerminalView, string?>(
                nameof(CurrentDirectory),
                o => o.CurrentDirectory);

        /// <summary>
        /// The font a terminal falls back to when nothing else is specified: a monospace stack, tried in
        /// order, ending at the platform's generic monospace family.
        /// </summary>
        /// <remarks>
        /// <see cref="FontFamily.Default"/> is the system UI font, which is proportional — and a terminal
        /// rendered in a proportional font is not merely ugly, it is wrong. The cell grid is derived from a
        /// single measured advance width, so glyphs that do not share that width drift out of their columns
        /// and box drawing, alignment and cursor positioning all come apart. A terminal control has to be
        /// usable without the consumer knowing to style it.
        /// </remarks>
        /// <remarks>
        /// The emoji families are at the END and never in front. The cell grid comes from the first family
        /// that exists on the machine, these are proportional, and one of them in that position breaks the
        /// grid rather than fixing the glyphs.
        ///
        /// They are named rather than left to the platform because the fallback picks badly for a joined
        /// sequence. With no emoji family in the chain, a cluster the monospace families cannot shape falls
        /// to whatever monochrome symbol font the system offers — and that font has the COMPONENTS without a
        /// ligature for the sequence, so a couple or a family is drawn as its separate parts, tinted by the
        /// terminal's foreground. That tint is the giveaway: a colour emoji carries its own colours, so
        /// anything wearing the foreground is not one.
        /// </remarks>
        public static readonly FontFamily DefaultFontFamily = new FontFamily(
            "Cascadia Mono,Cascadia Code,Consolas,Menlo,DejaVu Sans Mono,Liberation Mono,Courier New," +
            "Segoe UI Emoji,Apple Color Emoji,Noto Color Emoji,monospace");

        public static readonly StyledProperty<FontFamily> FontFamilyProperty =
            AvaloniaProperty.Register<TerminalView, FontFamily>(
                nameof(FontFamily),
                defaultValue: DefaultFontFamily);

        public static readonly StyledProperty<double> FontSizeProperty =
            AvaloniaProperty.Register<TerminalView, double>(
                nameof(FontSize),
                defaultValue: 12);

        public static readonly StyledProperty<FontStyle> FontStyleProperty =
            AvaloniaProperty.Register<TerminalView, FontStyle>(
                nameof(FontStyle),
                defaultValue: FontStyle.Normal);

        public static readonly StyledProperty<FontWeight> FontWeightProperty =
            AvaloniaProperty.Register<TerminalView, FontWeight>(
                nameof(FontWeight),
                defaultValue: FontWeight.Normal);

        public static readonly StyledProperty<TextDecorationLocation?> TextDecorationsProperty =
            AvaloniaProperty.Register<TerminalView, TextDecorationLocation?>(
                nameof(TextDecorations),
                defaultValue: null);

        public static readonly StyledProperty<IBrush> ForegroundProperty =
            AvaloniaProperty.Register<TerminalView, IBrush>(
                nameof(Foreground),
                defaultValue: Brushes.White);

        public static readonly StyledProperty<IBrush> BackgroundProperty =
            AvaloniaProperty.Register<TerminalView, IBrush>(
                nameof(Background),
                defaultValue: Brushes.Black);

        public static readonly StyledProperty<IBrush> SelectionBrushProperty =
            AvaloniaProperty.Register<TerminalView, IBrush>(
                nameof(SelectionBrush),
                defaultValue: new SolidColorBrush(Color.FromArgb(128, 0, 120, 215)));

        public static readonly StyledProperty<string> ProcessProperty =
            AvaloniaProperty.Register<TerminalView, string>(
                nameof(Process),
                defaultValue: RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? "cmd.exe" : "bash");

        public static readonly StyledProperty<IList<string>> ProcessArgsProperty =
            AvaloniaProperty.Register<TerminalView, IList<string>>(
                nameof(ProcessArgs),
                defaultValue: Array.Empty<string>());

        public static readonly StyledProperty<string?> StartingDirectoryProperty =
            AvaloniaProperty.Register<TerminalView, string?>(
                nameof(StartingDirectory),
                defaultValue: Environment.CurrentDirectory);

        public static readonly StyledProperty<Color> CursorColorProperty =
            AvaloniaProperty.Register<TerminalView, Color>(
                nameof(CursorColor),
                defaultValue: Colors.White);

        /// <summary>
        /// Whether the font's programming ligatures are drawn. Off by default — a host that wants
        /// them opts in.
        /// </summary>
        /// <remarks>
        /// <para>A switch because a ligature is a taste people hold opinions about: a joined
        /// ligature hides how many characters are actually there, which some people want and
        /// others find intolerable in code they are editing. Off by default so the terminal
        /// behaves exactly as it always has until a host decides otherwise.</para>
        /// <para>A font without them is unaffected either way — nothing to turn off, and nothing
        /// is spent looking: see <see cref="LigatureProbe"/>.</para>
        /// </remarks>
        public static readonly StyledProperty<bool> LigaturesProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(Ligatures),
                defaultValue: false);

        /// <summary>Whether the font's programming ligatures are drawn. See <see cref="LigaturesProperty"/>.</summary>
        public bool Ligatures
        {
            get => GetValue(LigaturesProperty);
            set => SetValue(LigaturesProperty, value);
        }

        /// <summary>
        /// Turns the font's ligatures off for one piece of text, when the switch says so.
        /// </summary>
        /// <remarks>
        /// <para>Only needed on the FormattedText path. Avalonia shapes that text, so ligatures
        /// arrive whether or not anyone asked — turning them OFF is the work. The fast path never
        /// needs this: it maps characters to glyphs one for one, so a ligature cannot form there,
        /// which is also why a run that SHOULD ligate has to decline it — see the run builder.</para>
        /// <para><c>calt</c> and <c>liga</c> both, because the two forms exist: programming fonts
        /// use contextual alternates, and a text face that reached a terminal might use real
        /// ligature substitution.</para>
        /// </remarks>
        private void ApplyLigatureSetting(FormattedText text)
        {
            if (!Ligatures)
                text.SetFontFeatures(LigaturesOff);
        }

        /// <summary>Built once: a collection per run per frame would be an allocation for nothing.</summary>
        private static readonly FontFeatureCollection LigaturesOff = new()
        {
            new FontFeature { Tag = "calt", Value = 0 },
            new FontFeature { Tag = "liga", Value = 0 },
        };

        /// <summary>
        /// Whether this text must reach the shaper for the ligature switch to be honoured. The
        /// glyph-run fast path maps characters to glyphs one for one, so a ligature can never form
        /// there; a run containing a character the font's ligature alphabet names has to take the
        /// FormattedText path while the switch is on. Fonts without ligatures — most — have a null
        /// alphabet and decline nothing, so they keep the fast path everywhere.
        /// </summary>
        private bool LigaturesWantShaping(string text, FontStyle style, FontWeight weight)
        {
            if (!Ligatures)
                return false;

            // The probe runs in the background on the first ask — never on this thread, which is
            // mid-paint. Until it answers, runs build exactly as they would with ligatures off;
            // when a real alphabet lands, the cached runs are stale by definition, so drop them
            // and the next frame rebuilds with the answer. A null answer changes nothing and never
            // calls back.
            var known = LigatureProbe.TryGetAlphabet(
                new Typeface(FontFamily, style, weight),
                _onLigatureAlphabetKnown ??= _ => global::Avalonia.Threading.Dispatcher.UIThread.Post(InvalidateRunCaches),
                out var alphabet);

            return known && alphabet is not null && LigatureProbe.ContainsCandidate(text, alphabet);
        }

        /// <summary>
        /// One stable callback per view, not a lambda per ask: a view asks once per run it builds,
        /// and the probe deduplicates waiters by delegate equality so each view is invalidated
        /// exactly once when the alphabet arrives.
        /// </summary>
        private Action<bool[]?>? _onLigatureAlphabetKnown;

        public static readonly StyledProperty<XT.Common.CursorStyle> CursorStyleProperty =
            AvaloniaProperty.Register<TerminalView, XT.Common.CursorStyle>(
                nameof(CursorStyle),
                defaultValue: XT.Common.CursorStyle.Bar);

        public static readonly StyledProperty<bool> CursorBlinkProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(CursorBlink),
                defaultValue: true);

        /// <summary>
        /// Off, like xterm's resource of the same name and like every flag in the emulator's own
        /// <c>WindowOptions</c>: rearranging the user's desktop is opt-in.
        /// </summary>
        public static readonly StyledProperty<bool> AllowWindowOpsProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(AllowWindowOps),
                defaultValue: false);

        /// <summary>
        /// Off, as on every other terminal: the tty's line discipline owns this, not the emulator.
        /// </summary>
        public static readonly StyledProperty<bool> ConvertEolProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(ConvertEol),
                defaultValue: false);

        public static readonly StyledProperty<int> CursorBlinkRateProperty =
            AvaloniaProperty.Register<TerminalView, int>(
                nameof(CursorBlinkRate),
                defaultValue: 530);

        /// <summary>
        /// When <see langword="false"/> (default), a plain single left-click does not
        /// immediately show a selection highlight. The selection only starts once the
        /// pointer moves, so casual clicks produce no visible caret artifact.
        /// Set to <see langword="true"/> to restore the original behaviour where a
        /// single-cell highlight appears on every click.
        /// Double- and triple-click (word / line selection) are unaffected by this setting.
        /// </summary>
        public static readonly StyledProperty<bool> ShowCaretOnClickProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(ShowCaretOnClick),
                defaultValue: false);

        public bool ShowCaretOnClick
        {
            get => GetValue(ShowCaretOnClickProperty);
            set => SetValue(ShowCaretOnClickProperty, value);
        }

        /// <summary>
        /// Which convention the terminal follows for Ctrl+A, Ctrl+C, Ctrl+V and Ctrl+X. Defaults to
        /// <see cref="ShortcutMode.Terminal"/>, which changes nothing.
        /// </summary>
        /// <remarks>
        /// See <see cref="ShortcutMode"/> for what each mode does and why the choice exists at all.
        /// </remarks>
        public static readonly StyledProperty<ShortcutMode> ShortcutModeProperty =
            AvaloniaProperty.Register<TerminalView, ShortcutMode>(
                nameof(ShortcutMode),
                defaultValue: ShortcutMode.Terminal);

        /// <inheritdoc cref="ShortcutModeProperty"/>
        public ShortcutMode ShortcutMode
        {
            get => GetValue(ShortcutModeProperty);
            set => SetValue(ShortcutModeProperty, value);
        }

        /// <summary>
        /// Hold the cursor back even when a process IS attached. Between spawning a shell and
        /// its first byte of output the buffer is still empty, so the cursor paints at (0,0) — which is
        /// wrong wherever the host layers something over the view during that window: an overlay drawing
        /// its own caret would leave the shell's stranded in the corner beneath it. Clear it once the shell
        /// has painted — <see cref="ShellReady"/> is the signal.
        /// </summary>
        public static readonly StyledProperty<bool> SuppressCursorProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(SuppressCursor),
                defaultValue: false);

        public bool SuppressCursor
        {
            get => GetValue(SuppressCursorProperty);
            set => SetValue(SuppressCursorProperty, value);
        }

        /// <summary>
        /// When <see langword="true"/>, <see cref="OutputReceived"/> is raised directly on the background
        /// read task instead of being marshalled to the UI thread. Default is <see langword="false"/>.
        /// </summary>
        /// <remarks>
        /// <para>Opt in when latency and ordering matter more than convenience — matching a dev server's
        /// "listening on :port" line to know when to open a browser, say. The dispatcher hop coalesces
        /// chunks and delivers them a frame or more late, which is fine for logging and not fine for that.</para>
        /// <para>The cost is that a handler then runs on the read task and MUST NOT touch UI without
        /// marshalling itself, and must not block — the loop that raises it is the one pumping output, so a
        /// slow handler stalls the terminal. The default is the safe one for exactly that reason.</para>
        /// </remarks>
        public static readonly StyledProperty<bool> OutputReceivedOnReadTaskProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(OutputReceivedOnReadTask),
                defaultValue: false);

        /// <inheritdoc cref="OutputReceivedOnReadTaskProperty"/>
        public bool OutputReceivedOnReadTask
        {
            get => GetValue(OutputReceivedOnReadTaskProperty);
            set => SetValue(OutputReceivedOnReadTaskProperty, value);
        }

        // Styled properties are UI-thread-affine, so the read task reads this mirror rather than the
        // property. Kept in step by OnPropertyChanged.
        private volatile bool _outputOnReadTask;

        /// <summary>
        /// When <see langword="true"/> (default), new output drags the viewport along so the terminal keeps
        /// showing the tail. Scrolling back pauses that until the view returns to the bottom; typing resumes
        /// it. Set to <see langword="false"/> and the terminal never scrolls itself.
        /// </summary>
        /// <remarks>
        /// Follow state is SAMPLED from the buffer immediately before each write rather than tracked as a
        /// flag. A flag has to be cleared by every path that can move the viewport, and missing one — the
        /// scrollbar, a programmatic <see cref="ViewportY"/> set, a resize — is invisible until somebody
        /// scrolls that exact way. Sampling covers all of them by construction.
        /// </remarks>
        public static readonly StyledProperty<bool> AutoScrollToBottomProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(AutoScrollToBottom),
                defaultValue: true);

        /// <inheritdoc cref="AutoScrollToBottomProperty"/>
        public bool AutoScrollToBottom
        {
            get => GetValue(AutoScrollToBottomProperty);
            set => SetValue(AutoScrollToBottomProperty, value);
        }

        /// <summary>
        /// OSC 133 — shell integration. Only the marker for "the prompt ends here" is acted on.
        /// </summary>
        /// <remarks>
        /// <para><c>B</c> is emitted by the shell immediately after it has drawn the prompt, so the cursor
        /// is standing exactly where the user's input will begin. That is the answer
        /// <see cref="NoteInputStart"/> spends effort inferring, and it is exact. Measured: after
        /// <c>OSC 133;B</c> following a 12-character prompt, the cursor is at column 12.</para>
        /// <para><c>I</c> is accepted alongside it, which some shells emit for the same point.</para>
        /// <para>Once a shell has reported this, the heuristic is disabled rather than left to compete: a
        /// shell that speaks OSC 133 knows better than any inference drawn from cursor movement.</para>
        /// <para>Runs on the read task, inside the terminal lock, so it does nothing but record.</para>
        /// </remarks>
        private void OnTerminalOscReceived(object? sender, XT.Events.TerminalEvents.OscReceivedEventArgs e)
        {
            if (e.Code != 133 || string.IsNullOrEmpty(e.Data))
                return;

            if (e.Data[0] is 'B' or 'I')
            {
                _inputStartRow = _terminal.Buffer.YBase + _terminal.Buffer.Y;
                _inputStartCol = _terminal.Buffer.X;
                _inputStartPending = false;
                _semanticPrompt = true;
            }
        }

        /// <summary>
        /// The scrollback ring dropped <paramref name="count"/> lines off the top, so every absolute index
        /// below shifted by that much. A following view is about to be scrolled to the bottom anyway; a view
        /// parked up in the scrollback is moved down by the same amount, so the content the user is reading
        /// stays under their eye instead of sliding upward as output arrives.
        /// </summary>
        private void OnBufferTrimmed(int count)
        {
            if (_followBottom || count <= 0)
                return;

            var y = _terminal.Buffer.ViewportY;
            if (y > 0)
                _terminal.Buffer.ViewportY = Math.Max(0, y - count);
        }

        /// <summary>
        /// True while the view is following the tail — the state in which new output drags the viewport
        /// along. Read it to drive a "jump to bottom" affordance's visibility.
        /// </summary>
        public bool IsFollowingTail => _followBottom;

        /// <summary>
        /// Write one of the view's OWN lines — an exit notice, a read error — under the same follow rules the
        /// read loop applies to process output, and invalidate.
        /// </summary>
        /// <remarks>
        /// <para>These lines used to scroll to the bottom whenever <see cref="AutoScrollToBottom"/> was on,
        /// which is not what that property promises: scrolling back pauses the follow until the view returns
        /// to the tail, and a process exiting is no reason to yank a user who is reading scrollback down to
        /// the end. It is also the most likely moment for it to happen, since a process exiting is exactly
        /// when somebody is scrolled up looking at what it printed.</para>
        /// <para>Sampled BEFORE the write for the same reason the read loop samples there: afterwards
        /// <c>YBase</c> has advanced, so a view that genuinely was at the tail reads as not-following.</para>
        /// </remarks>
        private void WriteOwnLine(string text)
        {
            lock (_terminalLock)
            {
                var oldY = _terminal.Buffer.ViewportY;

                _followBottom = _isAlternateBuffer || (_autoScroll && _terminal.Buffer.IsAtBottom);

                Interlocked.Increment(ref _liveWriteGeneration);
                _terminal.WriteLine(text);

                // Alternate-buffer apps position their own cursor and are left alone, as in the read loop.
                if (!_isAlternateBuffer)
                {
                    if (_followBottom)
                    {
                        _terminal.Buffer.ScrollToBottom();
                    }
                    else if (!_autoScroll && _terminal.Buffer.ViewportY != oldY)
                    {
                        // With auto-scroll off the emulator still advances ViewportY itself as YBase grows,
                        // so the position has to be held rather than merely not scrolled — see the read
                        // loop, where the same hunk exists for the same reason.
                        _terminal.Buffer.ViewportY = Math.Min(oldY, MaxScrollback);
                    }
                }
            }

            RequestPaint();
        }

        /// <summary>
        /// When <see langword="false"/> (default), each entry in <see cref="ProcessArgs"/> reaches the process as a
        /// distinct argument, quoted as necessary so it arrives exactly as written. Set to
        /// <see langword="true"/> to hand the process one command line built by joining the entries with
        /// spaces, and let it apply its own parsing rules.
        /// </summary>
        /// <remarks>
        /// <para>Named after the <c>PtyOptions</c> member it sets, because that is genuinely what it does: the
        /// command line is taken verbatim. It is not merely that quoting is skipped — the argument vector is
        /// collapsed into one string and rebuilt by somebody else's parser, which can change how many
        /// arguments there are.</para>
        /// <para>The default is faithful and is what nearly every caller wants. But it is also unavoidable
        /// without this, and some programs parse their command line by rules of their own — so a caller
        /// reproducing an exact command line, or driving a tool with non-standard argument conventions, needs
        /// a way out. Requested in #17.</para>
        /// <para><b>This setting only has an effect on Windows.</b> Windows processes receive a single command
        /// line string, so something has to decide how the arguments are joined into it. Unix passes an argument
        /// vector to <c>exec</c> directly — there is no string to build, nothing to quote, and nothing this
        /// setting could change. Measured on both, with the argument list <c>hello world</c>, <c>a"b</c>,
        /// <c>plain</c>: Windows yields those three unchanged when false and <c>hello</c>, <c>world</c>,
        /// <c>ab plain</c> when true, while Unix yields the three unchanged either way.</para>
        /// </remarks>
        public static readonly StyledProperty<bool> VerbatimCommandLineProperty =
            AvaloniaProperty.Register<TerminalView, bool>(
                nameof(VerbatimCommandLine),
                defaultValue: false);

        /// <inheritdoc cref="VerbatimCommandLineProperty"/>
        public bool VerbatimCommandLine
        {
            get => GetValue(VerbatimCommandLineProperty);
            set => SetValue(VerbatimCommandLineProperty, value);
        }

        /// <summary>
        /// Extra environment variables for the launched process. Null (default) launches it with the host's
        /// environment unchanged.
        /// </summary>
        /// <remarks>
        /// <para>These are MERGED into the environment the child would otherwise inherit, not substituted for
        /// it — measured on both platforms: setting one variable took the child's environment from 88 entries
        /// to 89 on Windows and 31 to 32 on Linux, with the inherited ones, including <c>PATH</c>, still
        /// present. So a caller can add or override a single variable without having to reconstruct an entire
        /// environment, which would be the easy way to launch a shell that cannot find anything.</para>
        /// <para>Named <c>EnvironmentVariables</c> rather than <c>Environment</c>, which is what the PTY layer
        /// calls it, for one concrete reason: a property called <c>Environment</c> shadows
        /// <see cref="System.Environment"/> for every subclass, so anyone deriving from this control and
        /// writing <c>Environment.GetEnvironmentVariable(...)</c> would get a compile error rather than the
        /// framework. <c>ProcessStartInfo.EnvironmentVariables</c> is the established .NET name for exactly
        /// this concept.</para>
        /// <para><c>TERM</c> and <c>COLORTERM</c> are supplied automatically (as <c>xterm-256color</c> and
        /// <c>truecolor</c>) when this dictionary does not carry them, because nothing else does — the PTY
        /// layer sets neither, and on Windows there is none in the environment to inherit. Put either in
        /// here to override it.</para>
        /// </remarks>
        /// <summary>
        /// The <c>TERM</c> given to a launched process when the caller supplies none.
        /// </summary>
        /// <remarks>
        /// What this terminal actually behaves like. Overridden by putting <c>TERM</c> in
        /// <see cref="EnvironmentVariables"/>.
        /// </remarks>
        public const string DefaultTermType = "xterm-256color";

        /// <summary>
        /// The <c>COLORTERM</c> given to a launched process when the caller supplies none.
        /// </summary>
        /// <remarks>
        /// <para>Not a contradiction of <see cref="DefaultTermType"/>. The two answer different questions:
        /// <c>TERM</c> names a terminfo entry, and <c>xterm-256color</c> describes the 256-entry indexed
        /// palette that terminfo can express; <c>COLORTERM</c> advertises DIRECT 24-bit colour, which
        /// terminfo has no standard way to state. Every modern terminal sets both -- Windows Terminal,
        /// kitty, alacritty and iTerm2 among them.</para>
        /// <para>Without it a program reads the terminfo entry, concludes 256 colours, and quantises its
        /// output to the palette. This terminal takes full RGB, so that would be throwing away colour it
        /// could have shown.</para>
        /// </remarks>
        public const string DefaultColorTerm = "truecolor";

        public static readonly StyledProperty<IDictionary<string, string>?> EnvironmentVariablesProperty =
            AvaloniaProperty.Register<TerminalView, IDictionary<string, string>?>(
                nameof(EnvironmentVariables),
                defaultValue: null);

        /// <inheritdoc cref="EnvironmentVariablesProperty"/>
        public IDictionary<string, string>? EnvironmentVariables
        {
            get => GetValue(EnvironmentVariablesProperty);
            set => SetValue(EnvironmentVariablesProperty, value);
        }

        /// <summary>The emulator options this view reads. See the property for the identity rules.</summary>
        /// <remarks>
        /// Owned by TerminalView, which it was not: it was registered against TerminalControl, which
        /// registers an Options of its OWN under that same owner and name. Two different
        /// StyledProperty objects then claimed one entry in the registry, so a style or a setter
        /// aimed at TerminalControl.Options could resolve to whichever was reached first, and nothing
        /// aimed at TerminalView.Options was aimed at this view at all.
        /// </remarks>
        public static readonly StyledProperty<XTerm.Options.TerminalOptions?> OptionsProperty =
            AvaloniaProperty.Register<TerminalView, XTerm.Options.TerminalOptions?>(
                nameof(Options),
                defaultValue: null);

        // ---- scrollback search, for a host's find box to drive ---------------------------------
        //
        // Methods and properties rather than gestures: the box, the debounce and the keybinding all
        // belong to the host. What lives here is the part only the terminal can do -- matching
        // against the buffer, painting the hits, and moving the viewport to one.

        /// <summary>
        /// Every match, painted so a search reads as a map of the output.
        /// </summary>
        /// <remarks>
        /// Translucent, like <see cref="SelectionBrush"/>, and drawn as an overlay after the text for
        /// the same reason: the glyphs stay exactly as they were and the tint reads through.
        /// </remarks>
        public static readonly StyledProperty<IBrush> SearchHighlightBrushProperty =
            AvaloniaProperty.Register<TerminalView, IBrush>(
                nameof(SearchHighlightBrush),
                defaultValue: new SolidColorBrush(Color.FromArgb(90, 240, 180, 41)));

        public IBrush SearchHighlightBrush
        {
            get => GetValue(SearchHighlightBrushProperty);
            set => SetValue(SearchHighlightBrushProperty, value);
        }

        /// <summary>The match the find box is standing on, distinct from the rest.</summary>
        public static readonly StyledProperty<IBrush> SearchCurrentBrushProperty =
            AvaloniaProperty.Register<TerminalView, IBrush>(
                nameof(SearchCurrentBrush),
                defaultValue: new SolidColorBrush(Color.FromArgb(160, 240, 180, 41)));

        public IBrush SearchCurrentBrush
        {
            get => GetValue(SearchCurrentBrushProperty);
            set => SetValue(SearchCurrentBrushProperty, value);
        }

        private XT.Search.BufferSearch? _search;
        private int _currentMatchId = -1;

        /// <summary>How many matches the last search found. See also <see cref="SearchTruncated"/>.</summary>
        public int SearchHitCount => _search?.Count ?? 0;

        /// <summary>Index of the current match, or -1 before one is chosen. The "3" of "3 of 47".</summary>
        public int SearchCurrentIndex => _search?.CurrentIndex ?? -1;

        /// <summary>
        /// Whether the match cap bit, so a find box can say "10,000+" instead of a number that has
        /// quietly stopped being true.
        /// </summary>
        public bool SearchTruncated => _search?.Truncated ?? false;

        /// <summary>
        /// Width in pixels of a margin down the left, for marking where commands began and how they
        /// ended. Zero, the default, means no gutter and no layout change at all.
        /// </summary>
        /// <remarks>
        /// Off unless a host asks for it, and then it is the host's brushes that decide what appears:
        /// a mark with no brush set draws nothing. There is no default glyph and no default colour,
        /// because "an exit status beside the command" is a design decision and this control has no
        /// business making it. A host that wants something other than a bar reads
        /// <see cref="VisibleMarks"/> and draws over the top instead.
        /// </remarks>
        public static readonly StyledProperty<double> GutterWidthProperty =
            AvaloniaProperty.Register<TerminalView, double>(nameof(GutterWidth), 0.0);

        public double GutterWidth
        {
            get => GetValue(GutterWidthProperty);
            set => SetValue(GutterWidthProperty, value);
        }

        /// <summary>Marks a prompt whose command has not finished, or reported no status.</summary>
        public static readonly StyledProperty<IBrush?> GutterPromptBrushProperty =
            AvaloniaProperty.Register<TerminalView, IBrush?>(nameof(GutterPromptBrush));

        public IBrush? GutterPromptBrush
        {
            get => GetValue(GutterPromptBrushProperty);
            set => SetValue(GutterPromptBrushProperty, value);
        }

        /// <summary>Marks a command that exited zero.</summary>
        public static readonly StyledProperty<IBrush?> GutterSuccessBrushProperty =
            AvaloniaProperty.Register<TerminalView, IBrush?>(nameof(GutterSuccessBrush));

        public IBrush? GutterSuccessBrush
        {
            get => GetValue(GutterSuccessBrushProperty);
            set => SetValue(GutterSuccessBrushProperty, value);
        }

        /// <summary>Marks a command that exited non-zero.</summary>
        public static readonly StyledProperty<IBrush?> GutterFailureBrushProperty =
            AvaloniaProperty.Register<TerminalView, IBrush?>(nameof(GutterFailureBrush));

        public IBrush? GutterFailureBrush
        {
            get => GetValue(GutterFailureBrushProperty);
            set => SetValue(GutterFailureBrushProperty, value);
        }

        /// <summary>
        /// Every shell-integration mark on the rows currently on screen.
        /// </summary>
        /// <remarks>
        /// What a host draws its own gutter, minimap or margin from. Handed over as data rather than
        /// rendered here, because "an exit status beside the command" is a design decision — a glyph,
        /// a colour, a change bar, nothing at all — and the terminal has no business making it.
        /// <see cref="GutterWidth"/> is the built-in answer for hosts that would rather not.
        /// </remarks>
        public IReadOnlyList<VisibleMark> VisibleMarks
        {
            get
            {
                var found = new List<VisibleMark>();
                var lines = _terminal.Buffer.Lines;
                var top = _terminal.Buffer.ViewportY;

                for (var row = 0; row < _terminal.Rows; row++)
                {
                    var bufferRow = top + row;
                    if (bufferRow < 0 || bufferRow >= lines.Length)
                        continue;

                    if (lines[bufferRow] is not { } line || !line.HasMarks)
                        continue;

                    foreach (var mark in line.Marks)
                        found.Add(new VisibleMark(row, bufferRow, mark.Kind, mark.ExitCode));
                }

                return found;
            }
        }

        /// <summary>A shell-integration mark on a row the viewport is showing.</summary>
        /// <param name="ViewportRow">Row on screen, 0 at the top.</param>
        /// <param name="BufferRow">The same row as an absolute buffer index, which survives scrolling.</param>
        /// <param name="Kind">Which of the four OSC 133 marks.</param>
        /// <param name="ExitCode">The status a CommandFinished reported, or null where none was.</param>
        public readonly record struct VisibleMark(
            int ViewportRow,
            int BufferRow,
            XT.Common.ShellIntegrationMark Kind,
            int? ExitCode);

        static TerminalView()
        {
            AffectsRender<TerminalView>(
                FontFamilyProperty,
                FontSizeProperty,
                FontStyleProperty,
                FontWeightProperty,
                TextDecorationsProperty,
                ForegroundProperty,
                BackgroundProperty,
                SelectionBrushProperty,
                BufferSizeProperty,
                ViewportYProperty,
                CursorColorProperty,
                CursorStyleProperty,
                CursorBlinkProperty,
                SuppressCursorProperty,   // toggling it must repaint immediately
                // The gutter: a brush change must repaint the marks, and a width change moves the
                // whole grid sideways -- it affects measure below as well, since columns come out
                // of the width.
                GutterWidthProperty,
                GutterPromptBrushProperty,
                GutterSuccessBrushProperty,
                GutterFailureBrushProperty,
                // A brush change must repaint live highlights -- the same missing-invalidation
                // class Copilot found on the gutter properties in the OSC work.
                SearchHighlightBrushProperty,
                SearchCurrentBrushProperty);

            AffectsMeasure<TerminalView>(
                GutterWidthProperty,
                FontFamilyProperty,
                FontSizeProperty,
                FontStyleProperty,
                FontWeightProperty,
                BufferSizeProperty);

            FocusableProperty.OverrideDefaultValue<TerminalView>(true);
        }

#pragma warning disable CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider adding the 'required' modifier or declaring as nullable.
        public TerminalView()
#pragma warning restore CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider adding the 'required' modifier or declaring as nullable.
        {
            Focusable = true;
            Loaded += OnLoaded;
            Unloaded += OnUnloaded;
            TextInputMethodClientRequested += OnTextInputMethodClientRequested;
        }

        protected override void OnInitialized()
        {
            // Sync terminal options with styled properties
            var options = Options ?? new XT.Options.TerminalOptions();

            options.CursorStyle = CursorStyle;
            options.CursorBlink = CursorBlink;
            options.CursorBlinkRate = CursorBlinkRate;

            // Same reason BufferSize is carried across below: OnPropertyChanged returns early until the
            // emulator exists, so a value set in an object initialiser or an early template binding never
            // reaches the mirror. Seeding here is what makes `new TerminalView { OutputReceivedOnReadTask
            // = true }` actually take effect.
            _outputOnReadTask = OutputReceivedOnReadTask;

            // BufferSize may already have been set — by a template binding, or by a host that configured the
            // view before it was initialised. The setter cannot reach the emulator that early because it does
            // not exist yet, so the value is carried across here instead of being silently lost.
            options.Scrollback = _bufferSize;

            // Off by default on EVERY platform now -- see ConvertEol, which carries the host's
            // choice. This used to be forced on everywhere but Windows, on the theory that a raw
            // pty delivers bare line feeds; what it actually did was take LNM away from programs.
            // The emulator asks `Options.ConvertEol || LineFeedMode`, so a host that hard-set this
            // left LNM half-wired: a program could set it and never reset it, and CSI 20 l did
            // nothing on macOS and Linux for anyone. Translating bare line feeds is the tty line
            // discipline's job (ONLCR on the slave); a transport that truly cannot do it can turn
            // the property on.
            options.ConvertEol = ConvertEol;

            // Foreground and Background ARE the terminal's default colour pair, so they are seeded into the
            // theme BEFORE the emulator is built rather than assigned afterwards. That is what makes them
            // the values SGR 39/49 resolve to, what OSC 10/11 report, and — the part an assignment after
            // construction would miss — what OSC 110/111 RESET to. Reset to a colour the host never chose
            // is how a program "restoring the defaults" ends up with white on black.
            SeedThemeFromBrushes(options.Theme);

            // OSC 22 is opt-in in the emulator, and the opt-in is the host saying it has somewhere to put
            // the shape: an emulator that answered the support query on its own would leave programs using
            // shapes that never appear. PointerShapeChanged is wired below, so the yes is true when given.
            options.PointerShapesEnabled = true;

            // The read-only geometry reports, on by default: a view always knows its cell and text-area
            // sizes and answers them itself when no handler does, and a client that sizes images by
            // CSI 16 t gets silence without them -- which shears every placeholder picture it draws.
            // The Set* window commands stay opt-in: a view embedded in someone's layout has no business
            // moving or resizing the window it happens to live in; TerminalWindow opts into those.
            options.WindowOptions.GetCellSizePixels = true;
            options.WindowOptions.GetWinSizeChars = true;
            options.WindowOptions.GetWinSizePixels = true;
            options.WindowOptions.GetScreenSizePixels = true;

            // One switch, both gates. The emulator has a flag per manipulation command, all off,
            // and AllowWindowOps is this control's single advertised answer to "may the program
            // rearrange the window" -- so a yes has to open the emulator's gate too. Without this
            // the switch governed only DECCOLM (whose re-grid lives behind a mode the program sets
            // for itself) and the XTERM move/resize/minimise family was discarded upstream before
            // the gated handlers ever ran; a host that set the one documented property got one
            // command out of nine.
            if (AllowWindowOps)
                EnableWindowManipulation(options.WindowOptions);

            _terminal = new XT.Terminal(options);

            // Point the property at the emulator's OWN options from here on. XTerm.NET snapshots what it
            // is constructed with, so `options` above is no longer the object the emulator reads -- and a
            // host that went on setting properties on it, which is the ordinary shape of XAML and of any
            // `terminal.Options.CursorBlink = true` after startup, would be writing into a copy nothing
            // consults. No exception, no warning: the setting simply stops working, which is worse than a
            // break that throws because the integration keeps compiling and keeps running.
            //
            // Assigning the live instance rather than special-casing the getter keeps this a real styled
            // property -- bindings, styles and the property system all go on working, and every reader
            // gets the object the emulator actually reads.
            //
            // SetCurrentValue rather than SetValue, to say redirect rather than take ownership. Note
            // that Avalonia is not WPF here: SetValue does NOT clear a binding on a styled property,
            // and a test that binds Options and pushes through it passes either way. So this is about
            // intent rather than a bug being fixed -- the value is being pointed at the emulator's
            // instance, not claimed on the host's behalf.
            //
            // Not everything on it is live even so, and that is XTerm.NET's contract rather than this
            // one's: Cols, Rows, and the initial theme are consumed while the emulator is built. Use
            // Resize for the dimensions. Scrollback, Theme and TabStopWidth ARE live as of XTerm.NET's
            // options audit, and BufferSize here forwards to Scrollback.
            SetCurrentValue(OptionsProperty, _terminal.Options);

            // Seeded here so it is never unset. Render replaces it every frame; this is only what the very
            // first one starts from, and what anything drawing before that frame would otherwise trip over.
            _palette = _terminal.Colors.Take();

            // A program can move the palette out from under the renderer with OSC 4 or OSC 10/11/12. The
            // cached runs hold resolved brushes, so they have to go with it.
            _terminal.Colors.ColorChanged += OnTerminalColorChanged;

            // The normal buffer's ring evicts its oldest lines once the scrollback fills, and every absolute
            // index shifts down with it. A view parked in the scrollback has to move with the eviction or the
            // content slides upward under the user while output keeps arriving.
            //
            // The INSTANCE is captured here, and only here, because this point runs exactly once and
            // the buffer object outlives detach/re-attach. The handler itself goes on through
            // SubscribeTerminalEvents with the rest: it is balanced on detach and re-armed on
            // re-attach against this same remembered object, so a re-parent can neither double the
            // handler — which would move a parked viewport by a MULTIPLE of the evicted count — nor
            // leave one behind. Leaving one behind is not merely untidy: Terminal is public, so a
            // host holding the emulator keeps the whole view alive through the subscription and goes
            // on calling back into a control that is off the tree.
            //
            // Both of those are what a second copy of this line cost while it was here as well: the
            // shared method subscribes it too, so the handler ran twice per eviction.
            _scrollbackBuffer = _terminal.Buffer;

            // Shell integration. A shell that emits OSC 133 says exactly where its prompt ends, which is the
            // one thing the input-start heuristic can only infer. Subscribed here for the same reason as
            // Trimmed above: this point runs exactly once, and the emulator outlives a detach/re-attach.
            _terminal.OscReceived += OnTerminalOscReceived;

            SubscribeTerminalEvents();

            // Setup cursor blink timer
            _cursorBlinkTimer = new DispatcherTimer
            {
                Interval = TimeSpan.FromMilliseconds(CursorBlinkRate)
            };
            _cursorBlinkTimer.Tick += OnCursorBlinkTick;

            // The animation clock. The emulator owns no timer -- it is driven entirely by Write --
            // so somebody has to tell it how much time has gone by, and that is a job for the side
            // with a render loop. It only runs while something is actually animating; see
            // SyncAnimationClock.
            _animationTimer = new DispatcherTimer
            {
                Interval = TimeSpan.FromMilliseconds(AnimationTickMilliseconds)
            };
            _animationTimer.Tick += OnAnimationTick;

            // Initialize IME client
            _inputMethodClient = new TerminalInputMethodClient(this);
        }

        /// <summary>
        /// How often the animation clock ticks, in milliseconds.
        /// </summary>
        /// <remarks>
        /// Finer than any plausible frame gap, because the emulator advances by ELAPSED time rather
        /// than one frame per tick -- so this bounds the jitter of a frame change, not the speed the
        /// animation runs at. A slow tick makes a 40ms animation stutter; it does not make it slow.
        /// </remarks>
        private const int AnimationTickMilliseconds = 16;

        private DispatcherTimer _animationTimer;

        /// <summary>
        /// Elapsed time since the last animation tick.
        /// </summary>
        /// <remarks>
        /// A stopwatch rather than two readings of the wall clock, because the wall clock is not
        /// monotonic: an NTP correction stepping it backwards would hand the emulator a negative
        /// interval to advance by. Nothing here needs to know what time it is, only how much of it
        /// has gone by, which is the question a stopwatch answers.
        /// </remarks>
        private readonly Stopwatch _animationClock = new();

        /// <summary>
        /// Starts or stops the animation clock to match whether anything is animating.
        /// </summary>
        /// <remarks>
        /// Called after output is processed, which is the only moment an animation can start or
        /// stop. A terminal showing nothing but text keeps no timer running at all.
        /// </remarks>
        private void SyncAnimationClock()
        {
            var wanted = _terminal.HasRunningAnimations();

            if (wanted == _animationTimer.IsEnabled)
                return;

            if (wanted)
            {
                // Reset the clock rather than counting the idle time: an animation started after a
                // quiet minute should begin at its first frame, not a minute into itself.
                _animationClock.Restart();
                _animationTimer.Start();
            }
            else
            {
                _animationTimer.Stop();
            }
        }

        private void OnAnimationTick(object? sender, EventArgs e)
        {
            var elapsed = _animationClock.Elapsed;
            _animationClock.Restart();

            // Through RequestPaint, so an atomic update holds an animation frame too. A picture
            // advancing mid-update would present the half-written screen underneath it, which is the
            // exact tearing this exists to stop -- and it arrives on a timer, so it is the one paint
            // path that can fire while an application is between BSU and ESU without being asked to.
            if (_terminal.AdvanceAnimations(elapsed))
                RequestPaint();

            // An animation that ran out of loops stops on its own, so the clock has to notice.
            SyncAnimationClock();
        }

        /// <summary>
        /// OSC 7: the shell reporting its working directory.
        /// </summary>
        /// <remarks>
        /// POSTED, never Invoked. This is raised from <c>Terminal.Write</c>, which the read loop calls
        /// from inside <c>lock (_terminalLock)</c> on the pty reader thread -- and the UI thread takes
        /// that same lock in <see cref="ClearScreen"/>, <see cref="CurrentLineText"/> and
        /// <c>WriteOwnLine</c>. A blocking Invoke here is therefore a DEADLOCK and not merely a stall:
        /// the reader waits for the UI thread while the UI thread waits for the lock the reader holds.
        /// The application freezes with no exception to look for.
        ///
        /// Nothing waits on the result -- it updates a property and notifies -- so posting costs a
        /// frame's latency and removes one half of the deadlock outright.
        /// </remarks>
        private void OnTerminalDirectoryChanged(object? sender, TerminalEvents.DirectoryChangeEventArgs e)
        {
            var directory = e.Directory;

            Dispatcher.UIThread.Post(() =>
            {
                var oldValue = _currentDirectory;
                _currentDirectory = directory;
                RaisePropertyChanged(CurrentDirectoryProperty, oldValue, _currentDirectory);
            });
        }

        /// <summary>
        /// Gets a value indicating whether the terminal is currently using the alternate screen buffer.
        /// </summary>
        public bool IsAlternateBuffer => _isAlternateBuffer;

        /// <summary>
        /// Gets or sets the terminal scrollback buffer size in lines.
        /// </summary>
        public int BufferSize
        {
            get => _bufferSize;
            set
            {
                // _terminal does not exist until OnInitialized, and a value can legitimately arrive before
                // then — a template binding is applied while the view is still initialising. Store it either
                // way; BuildTerminal reads _bufferSize when it constructs the emulator.
                if (_terminal != null)
                    _terminal.Options.Scrollback = value;

                SetAndRaise(BufferSizeProperty, ref _bufferSize, value);
                RequestPaint();
            }
        }

        /// <summary>
        /// The absolute line index of the top of the viewport in the buffer.
        /// 0 = top of buffer, higher values = scrolled forward towards current output.
        /// </summary>
        public int ViewportY
        {
            get => _terminal.Buffer.ViewportY;
            set
            {
                var oldValue = _terminal.Buffer.ViewportY;
                _terminal.Buffer.ViewportY = value;

                if (oldValue != _terminal.Buffer.ViewportY)
                {
                    RaisePropertyChanged(ViewportYProperty, oldValue, _terminal.Buffer.ViewportY);
                    RequestPaint();
                }
            }
        }

        /// <summary>
        /// Maximum scroll position (total buffer lines - viewport lines).
        /// This is the maximum value ViewportY can be.
        /// </summary>
        public int MaxScrollback
        {
            get
            {
                // Simple: total lines in buffer minus how many we can see
                var totalLines = _terminal.Buffer.Length;
                var viewportLines = _terminal.Rows;
                var max = Math.Max(0, totalLines - viewportLines);
                return max;
            }
        }

        public int ViewportLines => _terminal.Rows;

        public XTerm.Terminal Terminal => _terminal;

        public void Kill() => _ptyConnection?.Kill();

        /// <summary>
        /// Wipe the screen AND the scrollback back to an empty buffer, via the parser's own
        /// erase sequences. Call it when a session returns to dormant, so the sleeping view is genuinely
        /// blank behind whatever stand-in the host draws, instead of showing the dead output of the process
        /// that just exited underneath it.
        /// No-op before <see cref="OnInitialized"/> has run — a pooled view that was never attached has no
        /// buffer to wipe, and a host posting this at Background priority can land the job on a view that
        /// has since been detached (or was never realised at all).
        /// </summary>
        public void ClearScreen()
        {
            if (_terminal == null) return;

            lock (_terminalLock)
            {
                Interlocked.Increment(ref _liveWriteGeneration);
                _terminal.Write("\u001b[H\u001b[2J\u001b[3J");   // home · erase screen · erase scrollback
                _terminal.Buffer.ScrollToBottom();
            }
            RequestPaint();
        }

        /// <summary>
        /// The text of the row the cursor sits on, trailing blanks trimmed. Read it as a session goes
        /// dormant so the sleeping view can show the shell's REAL last prompt instead of a synthesized one.
        /// </summary>
        public string CurrentLineText
        {
            get
            {
                if (_terminal == null)
                    return string.Empty;

                lock (_terminalLock)
                {
                    var buffer = _terminal.Buffer;
                    var line = buffer.GetLine(buffer.YBase + buffer.Y);
                    if (line == null) return string.Empty;

                    var sb = new StringBuilder(line.Length);
                    for (int x = 0; x < line.Length; x++)
                        sb.Append(string.IsNullOrEmpty(line[x].Content) ? " " : line[x].Content);
                    return sb.ToString().TrimEnd();
                }
            }
        }

        /// <summary>
        /// Copy the selection and then remove it, when it is removable. Returns false when there was
        /// nothing to copy.
        /// </summary>
        /// <remarks>
        /// <para>Cut is copy plus exactly the deletion that typing over a selection performs, so the same
        /// limit applies: only a KEYBOARD selection can be removed, because a mouse selection may sit
        /// anywhere on screen — including the scrollback — with no fixed relationship to the shell's
        /// cursor.</para>
        /// <para>Where it cannot remove, it does NOTHING and returns false — the clipboard is not touched
        /// and the selection is left standing. Copying instead would be worse than failing: the selection
        /// would clear, the clipboard would fill, and the source would still be there, which reads as a
        /// completed cut right until the user goes looking for what they moved.</para>
        /// </remarks>
        public async Task<bool> CutAsync()
        {
            if (!_terminal.Selection.HasSelection)
                return false;

            // Asked BEFORE anything is done, and answered without doing it.
            //
            // A cut that quietly turns into a copy is worse than a cut that does not happen: the selection
            // clears, the clipboard fills, and the source is still there — which reads as a completed cut
            // right until the user goes looking for what they moved. So a selection that cannot be removed
            // is left entirely alone, clipboard included, and false says so.
            //
            // The question has to be asked without consuming the answer: TakeKeyboardSelectionDeletion
            // CLEARS the selection as it takes it, so calling it first leaves CopyAsync nothing to copy.
            if (!CanRemoveSelection)
                return false;

            if (!await CopyAsync().ConfigureAwait(false))
                return false;

            var deletion = TakeKeyboardSelectionDeletion();
            if (deletion.Length == 0)
                return false;

            await SendToPtyAsync(deletion).ConfigureAwait(false);
            return true;
        }

        /// <summary>
        /// Gets the exit code of the launched PTY process after it has terminated.
        /// </summary>
        public int ExitCode => _ptyConnection?.ExitCode ?? -1;

        private void OnSynchronizedOutputChanged(object? sender, XT.Events.TerminalEvents.SynchronizedOutputEventArgs e)
        {
            if (e.Active)
            {
                BeginAtomicUpdate();
            }
            else
            {
                // The one moment the buffer is both COMPLETE and OWNED: the application has just
                // said the frame is whole, and this handler runs from inside Terminal.Write on the
                // thread delivering it, so nothing can write until it returns. Captured before the
                // paint below is requested, so the paint has a whole frame to draw.
                _frameCapture.Publish(_terminal, Interlocked.Read(ref _liveWriteGeneration));

                EndAtomicUpdate();
            }
        }

        /// <summary>
        /// An application has declared the start of an atomic update — DEC private mode 2026.
        /// </summary>
        /// <remarks>
        /// <para>A timestamp rather than a timer, and that is a correctness fix rather than a
        /// tidying. This is raised from Terminal.Write, so it runs on the PTY READER thread, and
        /// what it used to do there was dispose one DispatcherTimer and create another — UI-owned
        /// state, mutated off the UI thread, once per frame for as long as an application
        /// double-buffers.</para>
        /// <para>Disposing a DispatcherTimer does not recall a tick it has already queued. So a
        /// timeout armed for frame N could fire during frame N+2, find <c>_atomicUpdate</c> true
        /// because a LATER update was open, and end that one early. Ending an update early paints
        /// a frame the application had not finished writing, which is a torn frame — and the faster
        /// the frames, the likelier the overlap, which is why it showed on the heaviest demo and
        /// not the lighter ones.</para>
        /// <para>Nothing here touches the dispatcher now. The deadline is checked where it is
        /// already free to check: see <c>RequestPaint</c>.</para>
        /// <para>Order matters, and so does the volatile on the flag. The timestamp is written
        /// first and the flag second; a reader tests the flag first and the timestamp second. The
        /// volatile write releases the timestamp with the flag, so no thread can see the update as
        /// open while still holding the PREVIOUS timestamp — or zero, whose elapsed time is the age
        /// of the process, which would look like a deadline blown the instant the update began and
        /// paint the half-written frame this exists to prevent. x64 would not reorder those two
        /// stores; arm64 is free to.</para>
        /// </remarks>
        private void BeginAtomicUpdate()
        {
            _atomicUpdateStartedAt = Stopwatch.GetTimestamp();
            _atomicUpdate = true;
        }

        private void EndAtomicUpdate()
        {
            if (!_atomicUpdate)
                return;

            _atomicUpdate = false;

            // One frame for the whole update, which is the point.
            RequestPaint();
        }

        public int Pid => _ptyConnection!.Pid;

        /// <summary>
        /// Gets or sets the font family used to render terminal text.
        /// </summary>
        public FontFamily FontFamily
        {
            get => GetValue(FontFamilyProperty);
            set => SetValue(FontFamilyProperty, value);
        }

        /// <summary>
        /// Gets or sets the font size used to render terminal text.
        /// </summary>
        public double FontSize
        {
            get => GetValue(FontSizeProperty);
            set => SetValue(FontSizeProperty, value);
        }

        /// <summary>
        /// Gets or sets the font style used to render terminal text.
        /// </summary>
        public FontStyle FontStyle
        {
            get => GetValue(FontStyleProperty);
            set => SetValue(FontStyleProperty, value);
        }

        /// <summary>
        /// Gets or sets the font weight used to render terminal text.
        /// </summary>
        public FontWeight FontWeight
        {
            get => GetValue(FontWeightProperty);
            set => SetValue(FontWeightProperty, value);
        }

        /// <summary>
        /// Gets or sets the text decoration locations applied to terminal text.
        /// </summary>
        public TextDecorationLocation? TextDecorations
        {
            get => GetValue(TextDecorationsProperty);
            set => SetValue(TextDecorationsProperty, value);
        }

        /// <summary>
        /// Gets or sets the default foreground brush used for terminal text.
        /// </summary>
        public IBrush Foreground
        {
            get => GetValue(ForegroundProperty);
            set => SetValue(ForegroundProperty, value);
        }

        /// <summary>
        /// Gets or sets the terminal background brush.
        /// </summary>
        public IBrush Background
        {
            get => GetValue(BackgroundProperty);
            set => SetValue(BackgroundProperty, value);
        }

        /// <summary>
        /// Gets or sets the brush used to render selected terminal text.
        /// </summary>
        public IBrush SelectionBrush
        {
            get => GetValue(SelectionBrushProperty);
            set => SetValue(SelectionBrushProperty, value);
        }

        /// <summary>
        /// Gets or sets the executable or shell to launch in the terminal.
        /// </summary>
        public string Process
        {
            get => GetValue(ProcessProperty);
            set => SetValue(ProcessProperty, value);
        }

        /// <summary>
        /// Gets or sets the command-line arguments passed to <see cref="Process"/> when launching.
        /// </summary>
        public IList<string> ProcessArgs
        {
            get => GetValue(ProcessArgsProperty);
            set => SetValue(ProcessArgsProperty, value);
        }

        /// <summary>
        /// Gets or sets the initial working directory used when the PTY process is started.
        /// </summary>
        public string? StartingDirectory
        {
            get => GetValue(StartingDirectoryProperty);
            set => SetValue(StartingDirectoryProperty, value);
        }

        /// <summary>
        /// Gets the current working directory reported by the running terminal session.
        /// </summary>
        public string? CurrentDirectory => _currentDirectory;

        /// <summary>
        /// Gets or sets the cursor color used when rendering the terminal caret.
        /// </summary>
        public Color CursorColor
        {
            get => GetValue(CursorColorProperty);
            set => SetValue(CursorColorProperty, value);
        }

        /// <summary>
        /// Gets or sets the cursor style used by the terminal.
        /// </summary>
        public XT.Common.CursorStyle CursorStyle
        {
            get => GetValue(CursorStyleProperty);
            set => SetValue(CursorStyleProperty, value);
        }

        /// <summary>
        /// Gets or sets a value indicating whether the terminal cursor should blink.
        /// </summary>
        public bool CursorBlink
        {
            get => GetValue(CursorBlinkProperty);
            set => SetValue(CursorBlinkProperty, value);
        }

        /// <summary>
        /// Gets or sets whether the program may move, resize or restack the window it is running in.
        /// </summary>
        /// <remarks>
        /// <para>Covers the whole XTERM window-operation family this view forwards to its host --
        /// move, resize (<c>CSI 8 t</c>), minimise, maximise, restore, raise, lower, fullscreen --
        /// and DECCOLM's 80/132 switch, which asks for a resize by the same route. One switch rather
        /// than eight, because the question a host is answering is a single one: may the program
        /// rearrange the user's desktop.</para>
        /// <para>Off by default, which is the convention already in force everywhere around it:
        /// xterm's resource of this name defaults off, and every flag in the emulator's own
        /// <c>WindowOptions</c> -- one per operation -- defaults off too, with this host enabling
        /// only the four that REPORT. An application that can resize and raise its own window does
        /// it at a moment the user did not choose, so it asks first.</para>
        /// <para>Refusal is silent, as xterm's is: nothing is raised, so no host acts, and a bare
        /// <see cref="TerminalView"/> with its own handler is covered as well as
        /// <c>TerminalWindow</c>. Reports are NOT affected -- a program asking how big the window is
        /// still gets a truthful answer, because refusing to be moved is not a reason to lie.</para>
        /// <para>The consequence to know about is DECCOLM. Switching to 132 columns re-grids the
        /// emulator before any of this is consulted, because that gate lives upstream behind a mode
        /// the program sets for itself. While this is off the grid widens and the window does not,
        /// so the extra columns are drawn past the edge and clipped -- which is what a host is
        /// choosing when it declines. Turn this on to have the window follow instead.</para>
        /// </remarks>
        public bool AllowWindowOps
        {
            get => GetValue(AllowWindowOpsProperty);
            set => SetValue(AllowWindowOpsProperty, value);
        }

        /// <summary>
        /// Opens the emulator's own per-command gate for the window-manipulation family, which is
        /// the second half of what <see cref="AllowWindowOps"/> promises: without these flags the
        /// emulator discards the commands before this control's gated handlers ever see them.
        /// </summary>
        /// <remarks>
        /// The manipulation commands only -- the Get* reports have their own defaults, set where the
        /// emulator is built, and refusing to be moved is not a reason to stop answering questions.
        /// The same set <c>TerminalWindow.EnableWindowCommands</c> turns on.
        /// </remarks>
        private static void EnableWindowManipulation(XTerm.Options.WindowOptions windowOptions)
        {
            windowOptions.SetWinPosition = true;
            windowOptions.SetWinSizePixels = true;
            windowOptions.SetWinSizeChars = true;
            windowOptions.RaiseWin = true;
            windowOptions.LowerWin = true;
            windowOptions.RefreshWin = true;
            windowOptions.RestoreWin = true;
            windowOptions.MaximizeWin = true;
            windowOptions.MinimizeWin = true;
            windowOptions.FullscreenWin = true;
        }

        /// <summary>
        /// Gets or sets whether a bare line feed also returns the carriage.
        /// </summary>
        /// <remarks>
        /// <para>Off, which is where every other terminal leaves it: translating a bare line feed is
        /// the tty line discipline's job (ONLCR on the slave), not the emulator's, and a pty that
        /// sends bare line feeds to a terminal is a pty that has not been set up. This host used to
        /// force it on for everything but Windows, which papered over that and cost more than it
        /// paid.</para>
        /// <para>What it cost: the emulator asks <c>Options.ConvertEol || LineFeedMode</c>, and LNM
        /// is the second half of that -- so while this is on, a program can SET LNM but never RESET
        /// it, and <c>CSI 20 l</c> does nothing at all. A program that resets LNM to move down a
        /// line WITHOUT returning the carriage gets the carriage return anyway and writes its whole
        /// line into column one. vttest's cursor-control screen builds a line exactly that way, and
        /// it collapsed to a single character on macOS and Linux for every host.</para>
        /// <para>Turn it on for a transport that really does deliver bare line feeds and cannot be
        /// fixed at its own layer. Set it BEFORE the emulator is built to have it apply from the
        /// first byte; changing it afterwards moves the live emulator too.</para>
        /// </remarks>
        public bool ConvertEol
        {
            get => GetValue(ConvertEolProperty);
            set => SetValue(ConvertEolProperty, value);
        }

        /// <summary>
        /// Gets or sets the cursor blink rate in milliseconds.
        /// </summary>
        public int CursorBlinkRate
        {
            get => GetValue(CursorBlinkRateProperty);
            set => SetValue(CursorBlinkRateProperty, value);
        }

        /// <summary>
        /// Gets or sets the terminal emulation options used to configure the inner <see cref="XTerm.Terminal"/>.
        /// </summary>
        public XTerm.Options.TerminalOptions? Options
        {
            get => GetValue(OptionsProperty);
            set => SetValue(OptionsProperty, value);
        }

        /// <summary>
        /// Seed the emulator's DEFAULT colour pair from <see cref="Foreground"/> and <see cref="Background"/>.
        /// </summary>
        /// <remarks>
        /// Written into the theme before construction, so these become the values the emulator resets to and
        /// not merely its current pair. Only a solid brush carries one colour to seed with; a gradient has no
        /// single answer, so the emulator keeps its own default rather than being handed an arbitrary stop.
        /// </remarks>
        private void SeedThemeFromBrushes(XT.Options.ThemeOptions theme)
        {
            if (Foreground is ISolidColorBrush fg)
                theme.Foreground = ToHex(fg.Color);

            if (Background is ISolidColorBrush bg)
                theme.Background = ToHex(bg.Color);

            static string ToHex(Color c) => $"#{c.R:X2}{c.G:X2}{c.B:X2}";
        }

        /// <summary>
        /// A program moved the palette. Cached runs hold brushes resolved from the old colours, so they are
        /// dropped rather than replayed.
        /// </summary>
        private void OnTerminalColorChanged(object? sender, EventArgs e)
        {
            // COALESCED, because the work is a walk of the whole scrollback and the trigger is one
            // escape sequence. A program setting the sixteen ANSI colours on startup -- which is what
            // every theme-setting shell profile does -- posted sixteen full-buffer walks, and a
            // buffer holding ten thousand lines made that O(sequences x lines) of UI-thread time for
            // an answer that is identical after the first.
            //
            // Only one is queued at a time, so the walk happens once for however many arrived.
            // Under the same lock the queue uses, because this is raised from BOTH threads: the pty
            // reader for an OSC palette sequence, and the UI thread through SyncPaletteToBrushes. A
            // plain check-and-set could have both find it false and queue two walks -- which is the
            // one thing the flag exists to prevent, arrived at by the shortest route.
            lock (_pendingHostCallbacks)
            {
                if (_paletteWalkQueued)
                    return;

                _paletteWalkQueued = true;
            }

            PostToHost(() =>
            {
                lock (_pendingHostCallbacks)
                {
                    _paletteWalkQueued = false;
                }

                // The same walk InvalidateRunCaches does, so it is called rather than repeated: two
                // copies of a loop over the whole buffer is one copy that goes stale.
                InvalidateRunCaches();
            });
        }

        /// <summary>Whether a full-buffer cache walk is already waiting to run.</summary>
        /// <remarks>Guarded by the queue's own lock; see OnTerminalColorChanged.</remarks>
        private bool _paletteWalkQueued;

        protected override void OnPropertyChanged(AvaloniaPropertyChangedEventArgs change)
        {
            // BEFORE the _terminal null-check below, deliberately. That guard returns early while the view
            // is still initialising, which is exactly when an object initialiser or a template binding sets
            // this — mirroring after it would silently drop the value and leave the reader following the
            // default forever.
            if (change.Property == AutoScrollToBottomProperty)
                _autoScroll = change.GetNewValue<bool>();

            // Once the emulator exists, this property IS its options, and assigning any other object
            // cannot reconfigure it -- XTerm.NET took its snapshot at construction and reads nothing
            // else. Rather than accept a write that would quietly go nowhere, the live instance is put
            // back, so every read gives the object the emulator actually consults.
            //
            // This is what keeps the invariant independent of ORDER. TerminalControl hands its own
            // Options down when the template is applied, which can happen after the view has already
            // built its emulator; without this the control's assignment would point the property back
            // at an object nothing reads. The recursion stops on the next pass, where the new value is
            // the instance being restored.
            if (change.Property == OptionsProperty && _terminal != null &&
                !ReferenceEquals(change.NewValue, _terminal.Options))
            {
                SetCurrentValue(OptionsProperty, _terminal.Options);
                return;
            }

            base.OnPropertyChanged(change);

            // _terminal and _cursorBlinkTimer are built in OnInitialized, and a cursor property can arrive
            // before that: the control template applies its bindings while the view is still initialising.
            // Nothing set these that early until TerminalControl began forwarding them, at which point this
            // threw a NullReferenceException from inside Avalonia's property machinery. Skipping here loses
            // nothing, because OnInitialized reads the current values when it builds the emulator.
            if (_terminal == null || _cursorBlinkTimer == null)
                return;

            if (change.Property == ForegroundProperty || change.Property == BackgroundProperty)
            {
                // Re-themed after the emulator was built, so the palette that answers OSC 10/11 has to move
                // with it. AffectsRender already covers the repaint; this is the emulator's own copy.
                SyncPaletteToBrushes();

                // And the cached runs, which hold brushes resolved from the OLD default. A repaint
                // replays them, so without this a re-theme changed the emulator's palette and left
                // every line already on screen drawn in the previous colours until something else
                // happened to invalidate it.
                //
                // SyncPaletteToBrushes covers the case it can: a solid brush becomes a palette entry,
                // and OnTerminalColorChanged then drops the caches. A brush it cannot express as RGB
                // -- a gradient, an image -- changes no palette entry, raises no colour change, and
                // so dropped nothing at all. That is the gap, and it is why this is unconditional
                // rather than only for the brushes that fail to convert.
                InvalidateRunCaches();
            }
            else if (change.Property == UseSkiaRendererProperty)
            {
                // Nothing cached needs purging -- the classic path's run caches stay valid for a
                // switch back -- but the frame on screen was drawn by the other path.
                InvalidateVisual();
            }
            else if (change.Property == ConvertEolProperty)
            {
                // Straight through to the live emulator: this is read on every line feed, so moving
                // it takes effect on the next one rather than needing a rebuild.
                _terminal.Options.ConvertEol = (bool)change.NewValue!;
            }
            else if (change.Property == LigaturesProperty)
            {
                // Every line's cached runs were built with the old setting, and the cache is
                // replayed rather than rebuilt — without the purge the switch would only reach
                // lines that happen to change afterwards, which looks like it half worked.
                InvalidateRunCaches();
            }
            else if (change.Property == AllowWindowOpsProperty && (bool)change.NewValue!)
            {
                // The same both-gates rule OnInitialized applies, for a host that says yes after the
                // emulator is built. One-way on purpose: revoking is already handled by the gated
                // handlers reading the CURRENT value, and TerminalWindow turns the emulator flags on
                // unconditionally -- turning them off here would fight it for no protection gained.
                EnableWindowManipulation(_terminal.Options.WindowOptions);
            }
            else if (change.Property == CursorStyleProperty)
            {
                _terminal.Options.CursorStyle = (XT.Common.CursorStyle)change.NewValue!;
            }
            else if (change.Property == CursorBlinkProperty)
            {
                var blink = (bool)change.NewValue!;
                _terminal.Options.CursorBlink = blink;

                if (blink && IsFocused)
                {
                    _cursorBlinkTimer.Start();
                }
                else
                {
                    _cursorBlinkTimer.Stop();
                    _cursorBlinkOn = true;  // Reset to visible when blinking stops
                }
            }
            else if (change.Property == OutputReceivedOnReadTaskProperty)
            {
                _outputOnReadTask = (bool)change.NewValue!;
            }
            else if (change.Property == CursorBlinkRateProperty)
            {
                var rate = (int)change.NewValue!;
                _terminal.Options.CursorBlinkRate = rate;
                _cursorBlinkTimer.Interval = TimeSpan.FromMilliseconds(rate > 0 ? rate : 530);
            }
        }

        private async void OnLoaded(object? sender, RoutedEventArgs e)
        {
            if (_ptyConnection == null && !string.IsNullOrEmpty(Process))
            {
                await LaunchProcess();
            }

            // Start cursor blinking if enabled
            if (CursorBlink)
            {
                _cursorBlinkTimer.Start();
            }

            // And the animation clock, which OnUnloaded stopped. Output is the only other thing
            // that starts it, so without this a view detached and re-attached -- a tab switched
            // away and back -- comes back with its animation frozen until something writes, which
            // at an idle prompt is never.
            SyncAnimationClock();
        }

        private void OnUnloaded(object? sender, RoutedEventArgs e)
        {
            // The search subscribes to Buffer.Trimmed, so it has to unhook when the view goes.
            _search?.Dispose();
            _search = null;
            _currentMatchId = -1;

            _cursorBlinkTimer.Stop();

            // A view off the tree has nothing to repaint, and a timer left running would hold it
            // alive through the dispatcher and go on advancing frames nobody can see.
            _animationTimer.Stop();

            _isSelecting = false;
            _pendingSelectionStart = null;
        }

        /// <summary>
        /// Call before removing this view from one visual tree and adding it to another.
        /// Prevents <see cref="OnDetachedFromLogicalTree"/> from killing the PTY process.
        /// Must be paired with <see cref="EndReparent"/> once re-attached.
        /// </summary>
        public void BeginReparent() => _suppressCleanupOnDetach = true;

        /// <summary>
        /// Call after the view has been re-attached to a new visual tree to restore
        /// normal cleanup behaviour and ensure render handlers are wired up.
        /// </summary>
        public void EndReparent() => _suppressCleanupOnDetach = false;

        /// <summary>
        /// Whether <see cref="Dispose"/> has run. A disposed view stops taking part in the logical
        /// tree rather than throwing from it — see <see cref="Dispose"/> for why.
        /// </summary>
        private bool _disposed;

        /// <summary>
        /// Releases the emulator, the process behind this view, and everything held with them.
        /// </summary>
        /// <remarks>
        /// <para>Explicit, and deliberately not wired to <see cref="OnDetachedFromLogicalTree"/>.
        /// Detach is not the end of a view's life here: this control supports being moved between
        /// panels, which is what <see cref="BeginReparent"/> exists for, and a view is also detached
        /// and re-attached during ordinary initialisation. Disposing on detach would kill a terminal
        /// that was only being moved. So whoever owns the view's lifetime calls this.</para>
        /// <para><c>XTerm.Terminal</c> holds parser subscriptions and event handlers that outlive
        /// every view that made one, which is what this is for. The pty, the cancellation source,
        /// the atomic-update timer and the cached bitmaps were already being released on detach;
        /// the emulator never was.</para>
        /// <para>Re-attaching a disposed view is a NO-OP rather than an exception. Avalonia raises
        /// logical-tree notifications during teardown in an order the application does not fully
        /// control, and throwing from a lifecycle hook takes down the app for what is at worst a
        /// view that will not paint. The guards below match the ones already there for a view whose
        /// emulator does not exist yet, which is the same shape of problem from the other end.</para>
        /// </remarks>
        public void Dispose()
        {
            if (_disposed)
                return;

            _disposed = true;

            // The Skia faces and fonts go HERE and not on visual detach. Detachment is not an
            // ownership boundary for this view -- it happens during ordinary initialisation and
            // during supported reparenting, both of which are followed by more painting -- and a
            // custom draw operation already queued still holds this cache on the render thread, so
            // disposing on detach could pull native handles out from under an in-flight composite.
            _skiaFonts.Dispose();

            // And the layer this view kept only to read its Unsupported report: it holds a snapshot,
            // its rows, and through them any images those rows referenced.
            _lastSkiaLayer = null;

            UnsubscribeTerminalEvents();

            // The two OnInitialized subscribes ONCE and re-attachment never restores, so they
            // belong here and not in the shared method above. Detach drops only what attach puts
            // back; dropping these there would leave a re-parented view permanently deaf to OSC
            // sequences and blind to palette changes, which is a worse bug than the leak.
            //
            // They are the rest of the leak all the same: a host holding the terminal after
            // disposing the view would otherwise keep calling into it through these two.
            //
            // Null-guarded, which the two lines below it were not. Everything OnInitialized builds
            // is absent on a view that was constructed and then dropped without ever being shown --
            // a host that decides against a tab it had already made, or any test that news up a view
            // and disposes it. UnsubscribeTerminalEvents guards for exactly this and so does the
            // _terminal?.Dispose() further down; these two did not, and threw between them. The
            // NullReferenceException was the smaller half of the damage: _disposed is already true
            // by then, so the rest of Dispose never ran and a second call could not run it either,
            // leaving the pty and the emulator held by a view the host believed it had released.
            if (_terminal != null)
            {
                _terminal.OscReceived -= OnTerminalOscReceived;
                _terminal.Colors.ColorChanged -= OnTerminalColorChanged;
            }

            // Both timers, because Dispose is not Unloaded. A view disposed while still on the tree
            // never gets an Unloaded, and DispatcherTimer holds its target through the Tick handler
            // -- so the timers keep the disposed view alive, and keep asking it to blink a cursor
            // and advance animations on an emulator that is about to be disposed underneath them.
            _cursorBlinkTimer?.Stop();
            _animationTimer?.Stop();

            _atomicUpdate = false;

            // Takes the pty, the cancellation source and the cached bitmaps with it. An ATTACHED
            // connection is still left alone, for the reason CleanupProcess gives: it belongs to
            // whoever attached it, and disposing it would stop a process this view does not own.
            CleanupProcess();

            _terminal?.Dispose();

            GC.SuppressFinalize(this);
        }

        /// <summary>
        /// Puts this view's handlers on the emulator.
        /// </summary>
        /// <remarks>
        /// <para>The exact mirror of <see cref="UnsubscribeTerminalEvents"/>, and it exists for the
        /// reason that one already gave for itself: a second copy of a list is a list that goes
        /// stale. There were two copies of the SUBSCRIBE list -- one for the first attach, one for a
        /// re-attach -- and they had drifted by exactly one entry.</para>
        /// <para>SynchronizedOutputChanged was in the re-attach copy and not the other, so DEC mode
        /// 2026 did nothing until a view had been detached and put back. A terminal that was never
        /// re-parented, which is nearly all of them, tore on every atomic update an application
        /// asked it not to tear on.</para>
        /// <para>What is deliberately NOT here: OscReceived and Colors.ColorChanged. Those are
        /// subscribed once, in OnInitialized, because a detach must not drop them -- see Dispose,
        /// which is the only thing that does.</para>
        /// </remarks>
        private void SubscribeTerminalEvents()
        {
            if (_terminal == null)
                return;

            if (_scrollbackBuffer != null)
                _scrollbackBuffer.Trimmed += OnBufferTrimmed;

            _terminal.DataReceived += OnTerminalDataReceived;
            _terminal.BufferChanged += OnTerminalBufferChanged;
            _terminal.CursorStyleChanged += OnTerminalCursorStyleChanged;
            _terminal.TitleChanged += OnTerminalTitleChanged;
            _terminal.StatusLineChanged += OnTerminalStatusLineChanged;
            _terminal.SynchronizedOutputChanged += OnSynchronizedOutputChanged;
            _terminal.WindowMoved += OnTerminalWindowMoved;
            _terminal.Resized += OnTerminalResized;
            _terminal.WindowResized += OnTerminalWindowResized;
            _terminal.WindowMinimized += OnTerminalWindowMinimized;
            _terminal.WindowMaximized += OnTerminalWindowMaximized;
            _terminal.WindowRestored += OnTerminalWindowRestored;
            _terminal.WindowRaised += OnTerminalWindowRaised;
            _terminal.WindowLowered += OnTerminalWindowLowered;
            _terminal.WindowFullscreened += OnTerminalWindowFullscreened;
            _terminal.BellRang += OnTerminalBellRang;
            _terminal.DirectoryChanged += OnTerminalDirectoryChanged;
            _terminal.ClipboardWriteRequested += OnTerminalClipboardWriteRequested;
            _terminal.ClipboardReadRequested += OnTerminalClipboardReadRequested;
            _terminal.NotificationReceived += OnTerminalNotificationReceived;
            _terminal.AttentionRequested += OnTerminalAttentionRequested;
            _terminal.PointerShapeChanged += OnTerminalPointerShapeChanged;
            _terminal.WindowInfoRequested += OnTerminalWindowInfoRequested;
        }

        /// <summary>
        /// Drops every handler this view put on the emulator.
        /// </summary>
        /// <remarks>
        /// Shared by detach and by <see cref="Dispose"/>, because they need exactly the same list and
        /// a second copy of it is a list that goes stale. Detach unsubscribes so a re-attached view
        /// can subscribe again; Dispose unsubscribes because there will be no re-attach.
        /// </remarks>
        private void UnsubscribeTerminalEvents()
        {
            if (_terminal == null)
                return;

            // Against the remembered instance, not _terminal.Buffer: unsubscribing while a full-screen
            // app has the alternate buffer active would otherwise let go of the wrong object.
            if (_scrollbackBuffer != null)
                _scrollbackBuffer.Trimmed -= OnBufferTrimmed;

            _terminal.DataReceived -= OnTerminalDataReceived;
            _terminal.BufferChanged -= OnTerminalBufferChanged;
            _terminal.CursorStyleChanged -= OnTerminalCursorStyleChanged;
            _terminal.TitleChanged -= OnTerminalTitleChanged;
            _terminal.StatusLineChanged -= OnTerminalStatusLineChanged;
            _terminal.SynchronizedOutputChanged -= OnSynchronizedOutputChanged;
            _terminal.WindowMoved -= OnTerminalWindowMoved;
            _terminal.Resized -= OnTerminalResized;
            _terminal.WindowResized -= OnTerminalWindowResized;
            _terminal.WindowMinimized -= OnTerminalWindowMinimized;
            _terminal.WindowMaximized -= OnTerminalWindowMaximized;
            _terminal.WindowRestored -= OnTerminalWindowRestored;
            _terminal.WindowRaised -= OnTerminalWindowRaised;
            _terminal.WindowLowered -= OnTerminalWindowLowered;
            _terminal.WindowFullscreened -= OnTerminalWindowFullscreened;
            _terminal.BellRang -= OnTerminalBellRang;
            _terminal.DirectoryChanged -= OnTerminalDirectoryChanged;
            _terminal.ClipboardWriteRequested -= OnTerminalClipboardWriteRequested;
            _terminal.ClipboardReadRequested -= OnTerminalClipboardReadRequested;
            _terminal.NotificationReceived -= OnTerminalNotificationReceived;
            _terminal.AttentionRequested -= OnTerminalAttentionRequested;
            _terminal.PointerShapeChanged -= OnTerminalPointerShapeChanged;
            _terminal.WindowInfoRequested -= OnTerminalWindowInfoRequested;
        }

        protected override void OnAttachedToLogicalTree(LogicalTreeAttachmentEventArgs e)
        {
            base.OnAttachedToLogicalTree(e);

            // Re-attaching a disposed view does nothing rather than resurrecting handlers onto an
            // emulator that has already let go of its own. See Dispose for why this is not a throw.
            if (_disposed)
                return;

            // _terminal is null during initial attachment (OnInitialized hasn't fired yet).
            // Only re-subscribe when re-parenting after a prior detach.
            if (_terminal == null) return;

            // The same list the once-only path uses, because it IS the same list. Unsubscribe
            // first, so a re-attach that follows an attach cannot double-subscribe.
            UnsubscribeTerminalEvents();
            SubscribeTerminalEvents();
        }

        private void OnCursorBlinkTick(object? sender, EventArgs e)
        {
            if (CursorBlink && IsFocused)
            {
                _cursorBlinkOn = !_cursorBlinkOn;

                // Over the VIEWPORT, not over buffer rows 0..Rows.
                //
                // GetLine takes an absolute buffer row, so 0..Rows is the oldest scrollback the
                // terminal has ever held -- lines nobody is looking at. On a fresh terminal the two
                // ranges coincide, which is why this looked right; the moment anything scrolls off
                // the top they diverge completely, and SGR 5 text stops blinking for the rest of the
                // session because the lines actually on screen keep their cached runs.
                var top = _terminal.Buffer.ViewportY;
                for (int y = 0; y < _terminal.Rows; y++)
                {
                    var line = _terminal.Buffer.GetLine(top + y);
                    if (line == null)
                        continue;

                    // A plain loop rather than Any(): this runs twice a second over every visible
                    // row, and the predicate closure was being allocated for each of them.
                    for (int x = 0; x < line.Length; x++)
                    {
                        if (line[x].Attributes.IsBlink())
                        {
                            line.Cache = null;
                            break;
                        }
                    }
                }

                // The status line blinks too -- vttest writes graphic renditions into it, SGR 5
                // included -- and it is not one of the viewport's lines, so the walk above never
                // reaches it. Without this its cached runs pin whichever phase was showing when
                // they were built, and the status line freezes half-lit.
                if (_statusLine is { } statusLine)
                {
                    for (int x = 0; x < statusLine.Length; x++)
                    {
                        if (statusLine[x].Attributes.IsBlink())
                        {
                            statusLine.Cache = null;
                            break;
                        }
                    }
                }

                RequestPaint();
            }
        }

        // macOS uses the Command (⌘ / Meta) key for clipboard shortcuts, following native
        // platform conventions (Terminal.app, iTerm2, etc.). Windows and Linux terminals use
        // Ctrl+Shift+C / Ctrl+Shift+V instead, because plain Ctrl+C is reserved for SIGINT.
        private static readonly bool IsMacOS = RuntimeInformation.IsOSPlatform(OSPlatform.OSX);

        protected override async void OnKeyDown(KeyEventArgs e)
        {
            // A TextInput belongs to the current stroke only. A previous non-text key may have
            // produced a Win32 record without ever producing TextInput, so do not let its marker
            // suppress a later IME commit.
            _win32RecordSentForThisStroke = false;

            // Only process input if this terminal has focus
            if (!IsFocused)
            {
                base.OnKeyDown(e);
                return;
            }

            // Capture the connection reference locally
            var ptyConnection = _ptyConnection;
            if (ptyConnection == null)
            {
                Debug.WriteLine($"[TerminalView] No PTY connection");
                base.OnKeyDown(e);
                return;
            }

            // When the process has exited, stop eating keyboard input so that Avalonia's
            // normal focus navigation (Tab/Shift+Tab etc.) works again.  We still handle
            // the copy shortcut so the user can copy terminal output after a run.
            // ShortcutMode.None hands the whole keyboard to the program: no copy, no paste, and Ctrl+C
            // reaching it as plain SIGINT because nothing intercepts it first.
            bool shortcuts = ShortcutMode != ShortcutMode.None;

            if (_processExitHandled != 0)
            {

                bool isCopy = shortcuts && e.Key == Key.C &&
                              (e.KeyModifiers == KeyModifiers.Control ||
                               e.KeyModifiers == (KeyModifiers.Control | KeyModifiers.Shift) ||
                               (IsMacOS && e.KeyModifiers == KeyModifiers.Meta));
                if (isCopy && _terminal.Selection.HasSelection)
                {
                    e.Handled = true;
                    // Copy leaves the selection in place, the way every other application does:
                    // copying is not a destructive act, and a selection you can no longer see is one
                    // you cannot copy again, extend, or replace.
                    await CopyAsync();
                    RequestPaint();
                }
                else
                {
                    base.OnKeyDown(e);
                }
                return;
            }

            try
            {
                // macOS clipboard shortcuts use the Command (Meta) key. These don't collide
                // with terminal control codes (SIGINT is Ctrl+C, not Cmd+C), so we can handle
                // them directly here. On Windows/Linux this block is skipped and the
                // Ctrl / Ctrl+Shift shortcuts below are used instead.
                if (shortcuts && IsMacOS && e.KeyModifiers == KeyModifiers.Meta)
                {
                    // Cmd+C - copy the selection (no-op when nothing is selected, matching macOS)
                    if (e.Key == Key.C)
                    {
                        e.Handled = true;
                        if (_terminal.Selection.HasSelection)
                        {
                            // Copy leaves the selection in place, the way every other application does:
                            // copying is not a destructive act, and a selection you can no longer see is one
                            // you cannot copy again, extend, or replace.
                            await CopyAsync();
                            RequestPaint();
                        }
                        return;
                    }

                    // Cmd+V - paste from the clipboard
                    if (e.Key == Key.V)
                    {
                        e.Handled = true;
                        await PasteAsync();
                        return;
                    }
                }

                // The macOS clipboard gestures are Cmd-based, and every one of them is unbound in a
                // terminal — so they are unconditional, like the Cmd+C and Cmd+V above. There is nothing to
                // take and so nothing to opt into.
                if (shortcuts && IsMacOS && e.KeyModifiers == KeyModifiers.Meta)
                {
                    if (e.Key == Key.X)
                    {
                        // Only claimed when it actually cuts. A selection it cannot remove — one made with
                        // the mouse, or sitting up in the scrollback — is left alone rather than quietly
                        // copied, so nothing looks like it moved when it did not.
                        //
                        // Asked SYNCHRONOUSLY, and claimed before the await rather than after it. This
                        // handler is async void: the first await returns to the caller and the routed
                        // event finishes bubbling with Handled still false, so the old placement claimed
                        // an event that had already gone -- Cmd+X cut the selection and reached the
                        // program as well. CanCut asks all three of the questions CutAsync asks
                        // before it does anything, which is what makes it safe to ask them here instead.
                        if (CanCut)
                        {
                            e.Handled = true;
                            await CutAsync().ConfigureAwait(false);
                            return;
                        }
                    }

                    if (e.Key == Key.A)
                    {
                        e.Handled = true;
                        await SelectInputAsync().ConfigureAwait(false);
                        return;
                    }
                }

                // The desktop map. Three things switch it off, each for its own reason.
                //
                // ShortcutMode, because these keys are contested and the host has to say which it wants.
                //
                // The ALTERNATE SCREEN, because a full-screen application owns its own keys: vim's Ctrl+V is
                // blockwise-visual, not paste. While one is running the terminal stands aside and behaves as
                // Terminal mode, so Ctrl+Shift+C still copies text out of it.
                //
                // macOS, because there the desktop clipboard lives on Cmd — handled above, in either mode —
                // while Ctrl+A and Ctrl+E are the system-wide emacs line bindings every macOS text field
                // honours. Leaving them to the program IS the desktop behaviour on that platform.
                if (ShortcutMode == ShortcutMode.Desktop && !IsMacOS && !_terminal.IsAlternateBufferActive)
                {
                    if (e.KeyModifiers == KeyModifiers.Control)
                    {
                        switch (e.Key)
                        {
                            case Key.A:
                                e.Handled = true;
                                await SelectInputAsync().ConfigureAwait(false);
                                return;

                            case Key.V:
                                e.Handled = true;
                                await PasteAsync().ConfigureAwait(false);
                                return;

                            case Key.X:
                                // Only when there is something to cut, and only when it can actually be
                                // removed. Otherwise the chord falls through to the program — where it is
                                // readline's prefix, and worth more than a cut that silently became a copy.
                                //
                                // Same correction as the macOS Cmd+X above: the question is asked
                                // synchronously so the claim can be made before the first await, which is
                                // the last moment anything is still listening for it. Here the old
                                // placement meant Ctrl+X cut the line AND handed readline its prefix.
                                if (CanCut)
                                {
                                    e.Handled = true;
                                    await CutAsync().ConfigureAwait(false);
                                    return;
                                }
                                break;
                        }
                    }

                    // Shift carries what the unshifted chord used to send: the literal control character.
                    if (e.KeyModifiers == (KeyModifiers.Control | KeyModifiers.Shift) && e.Key is Key.V or Key.X)
                    {
                        var literal = _terminal.GenerateCharInput(
                            e.Key == Key.V ? 'v' : 'x', XT.Input.KeyModifiers.Control);
                        if (!string.IsNullOrEmpty(literal))
                        {
                            e.Handled = true;
                            await SendToPtyAsync(literal).ConfigureAwait(false);
                            return;
                        }
                    }
                }

                // Handle Ctrl+C - copy if there's a selection, otherwise send SIGINT
                if (shortcuts && e.Key == Key.C && e.KeyModifiers == KeyModifiers.Control)
                {
                    if (_terminal.Selection.HasSelection)
                    {
                        e.Handled = true;
                        // Copy leaves the selection in place, the way every other application does:
                        // copying is not a destructive act, and a selection you can no longer see is one
                        // you cannot copy again, extend, or replace.
                        await CopyAsync();
                        RequestPaint();
                        return;
                    }
                    // No selection - fall through to send Ctrl+C (SIGINT) to the process
                }

                // Handle Ctrl+Shift+C for copy (always copies, doesn't send SIGINT)
                if (shortcuts && e.Key == Key.C && e.KeyModifiers == (KeyModifiers.Control | KeyModifiers.Shift))
                {
                    if (_terminal.Selection.HasSelection)
                    {
                        e.Handled = true;
                        // Copy leaves the selection in place, the way every other application does:
                        // copying is not a destructive act, and a selection you can no longer see is one
                        // you cannot copy again, extend, or replace.
                        await CopyAsync();
                        RequestPaint();
                        return;
                    }
                }

                // Typing means "put me back at the prompt" — every terminal jumps to the tail on input,
                // and without it a user who scrolled up types blind. Past the bare modifiers for the same
                // reason the selection-clear below skips them: pressing Ctrl on its own is not typing.
                if (!IsModifierKey(e.Key))
                    FollowTail();

                // Shift + navigation extends a selection in the buffer rather than sending the modified
                // cursor sequence (ESC[1;2C and friends), which no interactive shell binds — zsh just
                // echoes the ";2C" tail into the command line. Must come BEFORE the blanket clear below,
                // since this is the one keystroke family that GROWS a selection instead of dropping it.
                if (TryExtendKeyboardSelection(e))
                {
                    e.Handled = true;
                    return;
                }

                // Clear selection for any other keystroke - but ignore bare modifier
                // presses. Pressing ⌘/Ctrl/Shift on its own fires a KeyDown before the
                // shortcut's letter arrives; clearing here would lose the selection
                // before Cmd+C / Ctrl+Shift+C could copy it.
                if (!IsModifierKey(e.Key))
                {
                    // A keystroke that TYPES replaces the selection; Backspace and Delete remove it — both
                    // of them, as in any text field, where either key means "get rid of what is selected"
                    // rather than "act on one character". Anything else just drops the selection.
                    bool unmodified = (e.KeyModifiers & (KeyModifiers.Control | KeyModifiers.Alt | KeyModifiers.Meta)) == 0;
                    bool willType = unmodified && TryGetPrintableChar(e, out _);
                    bool willErase = unmodified && e.Key is Key.Back or Key.Delete;

                    if (willType || willErase)
                        NoteInputStart();

                    // Taken HERE and sent LATER, which makes every early return between this line
                    // and the senders a place the deletion can be lost -- while the selection it
                    // belonged to has already gone from the screen. Two of them were losing it: the
                    // Win32 and Kitty paths both claim the key and return, and both now carry it.
                    //
                    // The rest are safe by arithmetic rather than by luck: every other return in
                    // between requires Ctrl, Alt or Meta, and a modified keystroke neither types nor
                    // erases, so `unmodified` is false and this line has already stored empty. That
                    // is also why a value cannot go stale for long -- any non-modifier key
                    // reassigns it on the way past.
                    _pendingReplaceKeys = willType || willErase ? TakeKeyboardSelectionDeletion() : string.Empty;
                    if (_pendingReplaceKeys.Length == 0)
                    {
                        // The anchor is released whether or not a selection is currently drawn. A gesture can
                        // leave the anchor set having selected NOTHING — Shift+End at the end of a line, say —
                        // and gating this on HasSelection then leaves the caret pinned to that boundary while
                        // typed characters append somewhere else.
                        _kbSelAnchor = null;
                        _kbSelWholeInput = false;

                        if (_terminal.Selection.HasSelection)
                        {
                            _terminal.Selection.ClearSelection();
                            RequestPaint();
                        }
                    }
                }

                // Handle Ctrl+Shift+V for paste (standard terminal shortcut)
                // Ctrl+V is NOT intercepted - it gets passed to the application
                // (some apps use Ctrl+V for literal character input mode)
                if (shortcuts && e.Key == Key.V && e.KeyModifiers == (KeyModifiers.Control | KeyModifiers.Shift))
                {
                    e.Handled = true;
                    await PasteAsync();
                    return;
                }

                // Every other Meta chord belongs to the APPLICATION, not the shell. The macOS block above
                // claims Cmd+C and Cmd+V; anything else fell straight through to the character path below
                // and was typed into the process, so a host binding Cmd+K quietly sent the shell a "k".
                // Left unhandled so it bubbles to the app's key bindings.
                // Same reason as the selection alias above: a Mac keyboard has no Home/End, so Cmd+arrow
                // is how a Mac user asks for line-start and line-end. Sends exactly what Home and End
                // send, so it is an alias rather than a second code path — and it has to come BEFORE the
                // Meta passthrough below, which would otherwise swallow it.
                //
                // Not while Kitty is negotiated. This is a translation into what a SHELL binds, and
                // it is worth making only for a shell reading legacy sequences. An application that
                // asked for CSI-u reads Cmd+Left as a modified arrow in that encoding, and handing
                // it ESC[H instead sends a key nobody pressed, in a protocol it is no longer
                // reading. Falling through delivers the actual chord.
                if (IsMacOS && e.KeyModifiers == KeyModifiers.Meta && e.Key is Key.Left or Key.Right
                    && !_terminal.KittyKeyboardActive)
                {
                    e.Handled = true;
                    await SendToPtyAsync(e.Key == Key.Left ? "\u001b[H" : "\u001b[F").ConfigureAwait(false);
                    return;
                }

                // A legacy Meta chord belongs to the host application, so leave it unhandled. Once
                // Kitty is active, however, Meta is part of the protocol's key event and must reach
                // TrySendKittyKeyAsync below. Returning here would make Cmd+Left/Right disappear: the
                // shell alias above correctly declines it, then this guard would drop it before CSI-u.
                if ((e.KeyModifiers & KeyModifiers.Meta) != 0 && !_terminal.KittyKeyboardActive)
                    return;

                // Alt/Ctrl + Left/Right — "move by word". What the emulator generates for these is a
                // modified-cursor sequence (ESC[1;3D, ESC[1;5D) that no default shell keymap binds, so zsh
                // echoes the ";3D" tail straight into the command line. ESC-b / ESC-f — backward-word and
                // forward-word — is what zsh, bash's readline, fish and PSReadLine's default emacs mode all
                // bind out of the box, so that is what these chords send.
                //
                // Left alone in the alternate buffer, where a full-screen app reads the real sequence itself.
                //
                // And left alone when the process is reading WIN32 INPUT RECORDS. cmd.exe turns that mode on
                // as it starts (CSI ?9001h), and both it and PSReadLine already move by word on a real
                // Ctrl+Left — while neither binds ESC-b. Translating here replaced a chord they understand
                // with one they ignore, so on Windows the key did nothing at all. Falling through hands them
                // the actual key event a few lines below.
                // And not while Kitty is negotiated, for the same reason as the macOS chord above and
                // the same reason Win32 input mode is already excluded here: every exclusion on this
                // list is a transport the shell is not reading ESC-b through. An application that
                // negotiated CSI-u reads Alt+Left as a modified arrow and binds it itself; ESC-b is
                // a key it never pressed.
                if (e.Key is Key.Left or Key.Right
                    && e.KeyModifiers is KeyModifiers.Alt or KeyModifiers.Control
                    && !_terminal.Win32InputMode
                    && !_terminal.KittyKeyboardActive
                    && !_terminal.IsAlternateBufferActive)
                {
                    e.Handled = true;
                    await SendToPtyAsync(e.Key == Key.Left ? "\u001bb" : "\u001bf").ConfigureAwait(false);
                    return;
                }

                var modifiers = ConvertAvaloniaModifiers(e.KeyModifiers);
                var hasAlt = (modifiers & XT.Input.KeyModifiers.Alt) != 0;

                // Windows ConPTY limitation: There is no VT sequence for plain ESCAPE key.
                // When ENABLE_VIRTUAL_TERMINAL_INPUT is enabled (by cmd.exe), the only way
                // to send ESCAPE is via Win32 INPUT_RECORD format. Always use Win32 for ESC on Windows.
                bool isWindows = RuntimeInformation.IsOSPlatform(OSPlatform.Windows);
                bool isEscapeKey = e.Key == Key.Escape;
                // The Escape exception does NOT apply while Kitty is negotiated. It exists because
                // ConPTY has no VT sequence for a plain Escape, so Win32 records are the only way to
                // deliver one -- but an application that asked for CSI-u is not reading VT sequences
                // for Escape either, it is reading CSI 27 u, and the terminal can send that. Without
                // this, every Escape on Windows took the Win32 path and a negotiated application
                // never received the encoding it had asked for.
                //
                // Win32 input MODE keeps its precedence unconditionally: that is a different
                // transport rather than a competing encoding, and a process reading INPUT_RECORDs is
                // reading them for every key.
                bool useWin32Format = _terminal.Win32InputMode
                                      || (isWindows && isEscapeKey && !_terminal.KittyKeyboardActive);

                if (useWin32Format)
                {
                    var sequence = GenerateWin32InputSequence(e, isKeyDown: true);
                    if (!string.IsNullOrEmpty(sequence))
                    {
                        e.Handled = true;

                        // Carrying the pending deletion, for the reason given where it is taken: the
                        // selection was consumed several branches above, and an exit that sends the
                        // keystroke WITHOUT it types over a selection that silently never went away.
                        // Backspace and Delete replace their own sequence rather than adding to it --
                        // the selection is what they were asked to remove, not one character past it.
                        var erase = _pendingReplaceKeys;
                        _pendingReplaceKeys = string.Empty;

                        var toSend = erase.Length > 0 && e.Key is Key.Back or Key.Delete
                            ? erase
                            : erase + sequence;

                        // Noted so the TextInput that may follow knows this keystroke has already
                        // been reported, and does not send the same character a second time.
                        _win32RecordSentForThisStroke = true;

                        await SendToPtyAsync(toSend).ConfigureAwait(false);
                        return;
                    }
                    // If we couldn't generate a Win32 sequence, fall through to normal handling
                    // This can happen for keys that don't have a virtual key mapping
                }

                // The Kitty keyboard protocol, when an application has negotiated it. Ahead of every
                // legacy generator below, because once the flags are set those encodings are not what
                // the application is reading any more -- it asked for CSI-u and the terminal accepted
                // on this host's behalf. Behind the Win32 path above, which is a different protocol
                // for a different transport and keeps its precedence.
                //
                // The pending deletion travels WITH it. Kitty claims the key and returns, so a
                // deletion left behind here is one the shell never receives -- while the selection
                // it belonged to has already been cleared on screen. Handed over rather than taken
                // first, because this can also decline the key, and a deletion consumed by a call
                // that declined is one the legacy paths below would then send without.
                if (await TrySendKittyKeyAsync(e, XT.Input.KittyKeyboardEventType.Press,
                                               _pendingReplaceKeys).ConfigureAwait(false))
                {
                    _pendingReplaceKeys = string.Empty;
                    return;
                }

                // Convert Avalonia key to XTerm key
                var xtermKey = ConvertAvaloniaKeyToXTermKey(e.Key);

                // Special keys (arrows, function keys, Tab, etc.) - always handle in KeyDown
                if (xtermKey != null)
                {
                    // Backspace or Delete over a selection removes the SELECTION, not one more character
                    // beyond it — so the keystroke's own sequence is replaced rather than added to.
                    var erase = _pendingReplaceKeys;
                    _pendingReplaceKeys = string.Empty;
                    if (erase.Length > 0 && e.Key is Key.Back or Key.Delete)
                    {
                        e.Handled = true;
                        await SendToPtyAsync(erase).ConfigureAwait(false);
                        return;
                    }

                    var sequence = _terminal.GenerateKeyInput(xtermKey.Value, modifiers);
                    if (!string.IsNullOrEmpty(sequence))
                    {
                        e.Handled = true;
                        await SendToPtyAsync(sequence).ConfigureAwait(false);
                    }
                    return;
                }

                // AltGr FIRST, because Windows and X11 both report it as Ctrl+Alt and the block below
                // would otherwise turn a perfectly ordinary character into a control code. On a German
                // layout AltGr+Q is @, on a French one AltGr+0 is @, and every one of them arrived
                // here as Ctrl+Alt and left as NUL. Whole layouts could not type their own symbols.
                if (IsAltGrComposed(e, out var altGrChar))
                {
                    e.Handled = true;

                    // The character itself, with no modifiers -- because that is what the user typed.
                    // The Ctrl and Alt are an artefact of how the platform spells AltGr, not part of
                    // what was pressed.
                    var replacedByAltGr = _pendingReplaceKeys;
                    _pendingReplaceKeys = string.Empty;
                    await SendToPtyAsync(replacedByAltGr + altGrChar).ConfigureAwait(false);
                    return;
                }

                // Ctrl/Alt + character combinations (these don't generate TextInput events)
                if ((modifiers & (XT.Input.KeyModifiers.Control | XT.Input.KeyModifiers.Alt)) != 0)
                {
                    if (TryGetPrintableChar(e, out var keyChar))
                    {
                        var sequence = _terminal.GenerateCharInput(keyChar, modifiers);
                        if (!string.IsNullOrEmpty(sequence))
                        {
                            e.Handled = true;
                            await SendToPtyAsync(sequence).ConfigureAwait(false);
                        }
                    }
                    return;
                }

                // Try to get a printable character - first from KeySymbol, then from key mapping
                // This is critical for Consolonia where KeySymbol may be empty
                if (TryGetPrintableChar(e, out var printableChar))
                {
                    e.Handled = true;
                    // One write: the deletion and the character replacing it, in that order.
                    var replaced = _pendingReplaceKeys;
                    _pendingReplaceKeys = string.Empty;
                    await SendToPtyAsync(replaced + printableChar).ConfigureAwait(false);
                    return;
                }

                // If we couldn't handle it, let TextInput try (for desktop Avalonia)
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"[{_instanceId}] Error handling key input: {ex.Message}");
            }
        }

        /// <summary>
        /// The keystrokes that remove what a keyboard selection covers, so that typing over a selection
        /// REPLACES it the way it does in a text field. Empty when there is nothing to replace. Clears the
        /// selection as it takes it.
        /// </summary>
        /// <remarks>
        /// <para>The view cannot edit the line: the shell owns it. So the selection is turned into the
        /// keystrokes a user would have pressed to remove it. The shell's cursor never moved from the
        /// anchor, so a backwards selection is that many Backspaces; a forwards one walks the cursor to the
        /// far end with the right arrow first and deletes backwards from there.</para>
        /// <para>Backspace for both directions rather than Delete for the forward case, because
        /// forward-delete is not reliably bound: zsh started with no rc file does not know ESC[3~ — it
        /// swallows the ESC[3 and TYPES the tilde. Arrows and Backspace are bound everywhere.</para>
        /// <para>Returned rather than sent, so the caller can write the deletion and the new character as
        /// ONE write. Sending them separately loses the race against the next keystroke: the handler owning
        /// the deletion awaits it while the handlers behind it queue their characters first, and "there"
        /// typed over a selection arrives as "heret". Measured, not theorised.</para>
        /// <para>Only a KEYBOARD selection qualifies. A mouse selection can sit anywhere on screen,
        /// including the scrollback, with no fixed relationship to the shell's cursor, so typing over one
        /// clears it without deleting. The alternate buffer is excluded: a full-screen app owns its own
        /// editing.</para>
        /// </remarks>
        /// <summary>
        /// Whether the current selection is one this view can remove — the same conditions
        /// <see cref="TakeKeyboardSelectionDeletion"/> applies, asked without consuming them.
        /// </summary>
        private bool CanRemoveSelection
            => _kbSelAnchor is not null
               && _terminal.Selection.HasSelection
               && !_terminal.IsAlternateBufferActive
               && _kbSelAnchor.Value != _kbSelFocus;

        /// <summary>
        /// Whether <see cref="CutAsync"/> will succeed, asked without starting it.
        /// </summary>
        /// <remarks>
        /// <para>Exists so the key handlers can claim the chord BEFORE their first await, which is
        /// the last moment anything is still listening for the flag. Claiming afterwards means the
        /// event has already finished bubbling and the chord reaches the program as well.</para>
        /// <para>CanRemoveSelection alone was not enough for that. Cut can still decline after it --
        /// with no clipboard to write to, or a selection whose text is empty -- and a chord claimed
        /// on the strength of a cut that then did not happen is swallowed for nothing. Both of those
        /// are answerable here, synchronously, so this asks all three of the questions CutAsync asks
        /// rather than the first one.</para>
        /// <para>The last condition is the one that is easy to miss: the deletion has to be
        /// ENCODABLE. EncodeSyntheticKey answers empty when the live protocol has no way to express
        /// a synthetic Backspace, and a cut claimed past that point would have copied to the
        /// clipboard and then removed nothing -- a cut that silently became a copy, which is the
        /// outcome CutAsync exists to refuse.</para>
        /// <para>What is left is only the write itself failing, which nothing can predict.</para>
        /// </remarks>
        private bool CanCut
            => CanRemoveSelection
               && TopLevel.GetTopLevel(this)?.Clipboard is not null
               && !string.IsNullOrEmpty(_terminal.Selection.GetSelectionText())
               && !string.IsNullOrEmpty(BuildKeyboardSelectionDeletion());

        /// <summary>
        /// The bytes for one press of a key this view is pressing on the user's behalf, encoded for
        /// whichever keyboard protocol is live right now.
        /// </summary>
        /// <remarks>
        /// <para>The selection deletion is made of keystrokes nobody typed: Backspaces and right
        /// arrows standing in for an edit this view cannot perform itself, because the shell owns
        /// the line. They have to be encoded the way the application is currently READING
        /// keystrokes, and there are three answers to that, not one.</para>
        /// <para>Generating the legacy byte unconditionally — which is what this did first — is
        /// wrong twice over. Under Win32 input mode the process is reading INPUT_RECORDs and a bare
        /// 0x08 is not one, so cmd.exe and PSReadLine see nothing. Under a negotiated Kitty
        /// protocol the application asked for CSI-u and stopped reading the legacy encodings the
        /// terminal had been accepting on its behalf.</para>
        /// <para>Empty means this protocol cannot express the key, and the caller must then leave
        /// the selection ALONE rather than clearing it: a deletion that cannot be sent must not be
        /// drawn as though it happened.</para>
        /// </remarks>
        private string EncodeSyntheticKey(Key avaloniaKey, XT.Input.Key xtermKey, string kittyName)
        {
            // Win32 first, matching the precedence the real key path uses a few hundred lines up:
            // it is a different transport rather than a competing encoding, so it wins.
            if (_terminal.Win32InputMode)
            {
                var vk = ConvertAvaloniaKeyToVirtualKey(avaloniaKey);
                if (vk == 0)
                    return string.Empty;

                // A real key produces a down record and an up record, so a synthetic one has to as
                // well -- PSReadLine reads the pair. Scan code 0 for the same reason the real path
                // uses 0: there is no hardware event here to take one from.
                var unicode = avaloniaKey == Key.Back ? 0x08 : 0;

                // Through the same state builder a real key uses, rather than None. No modifier is
                // held for a synthetic key, but the control-key state carries more than modifiers:
                // the ENHANCED flag marks the extended-scan-code keys, and the right arrow this
                // sends for a forward selection is one of them. A record without it describes a
                // different key, and the console layer is entitled to read it as one.
                var state = GetWin32ControlKeyState(KeyModifiers.None, avaloniaKey);

                return Win32Record(vk, 0, unicode, isKeyDown: true, state)
                     + Win32Record(vk, 0, unicode, isKeyDown: false, state);
            }

            if (_terminal.KittyKeyboardActive)
            {
                // Both keys this is called with are in the protocol's fixed name table, so the name
                // is passed in rather than reached for through KittyKeyName -- that one needs a
                // KeyEventArgs for its KeySymbol fallback, and there is no event here.
                var ev = new XT.Options.KeyEvent { Key = kittyName, Code = kittyName };

                // Null is the generator saying the negotiated flags do not change this key, and the
                // legacy encoding is still what the application reads -- not that it sends nothing.
                var press = _terminal.GenerateKittyKeyInput(ev, XT.Input.KittyKeyboardEventType.Press)
                            ?? _terminal.GenerateKeyInput(xtermKey, XT.Input.KeyModifiers.None);

                // A release only if the flags asked for one. Sending it unconditionally would give
                // an application that never opted in a key-up it has no encoding for.
                var release = _terminal.GenerateKittyKeyInput(ev, XT.Input.KittyKeyboardEventType.Release);

                return press + release;
            }

            return _terminal.GenerateKeyInput(xtermKey, XT.Input.KeyModifiers.None);
        }

        /// <summary>
        /// The highest boundary a keyboard selection may reach: just past the last written cell at or after
        /// the input start.
        /// </summary>
        /// <remarks>
        /// A terminal grid is padded to full width with blanks, so without this Shift+Right walks off the
        /// end of the input and selects the empty rest of the screen a cell at a time. There is nothing
        /// there to select, and nothing the replace could do with it.
        ///
        /// Scanned backwards from the end so a wrapped input — which spans rows — is bounded by its real
        /// end rather than by the row the caret happens to be on. Wide glyphs count their placeholder, for
        /// the same reason <see cref="LineEndBoundary"/> does.
        ///
        /// <para>KNOWN LIMIT: a trailing space the user typed is not counted, so a selection stops just
        /// before it. There is no way to do better here — the emulator fills unwritten cells with spaces,
        /// and a typed space is identical to one of those in every respect. Measured: both carry
        /// <c>Content == " "</c>, <c>Width == 1</c> and <c>CodePoint == 32</c>. Distinguishing them needs
        /// the buffer to record that a cell was written, which is a change in XTerm.NET rather than
        /// here.</para>
        /// </remarks>
        private int InputEndBoundary(int cols, int lastBoundary)
        {
            int floor = InputStartBoundary(cols, lastBoundary);

            for (int b = lastBoundary - 1; b >= floor; b--)
            {
                int row = b / cols;
                int col = b % cols;
                var line = _terminal.Buffer.GetLine(_terminal.Buffer.ViewportY + row);
                if (line == null || col >= line.Length)
                    continue;

                var cell = line[col];
                if (!string.IsNullOrWhiteSpace(cell.Content))
                    return Math.Min(b + Math.Max(1, cell.Width), lastBoundary);
            }

            return floor;
        }

        protected override async void OnTextInput(TextInputEventArgs e)
        {
            // Only process input if this terminal has focus
            if (!IsFocused)
            {
                Debug.WriteLine($"[TerminalView] OnTextInput: Not focused, passing to base");
                base.OnTextInput(e);
                return;
            }

            // Capture the connection reference locally
            var ptyConnection = _ptyConnection;
            if (ptyConnection == null || string.IsNullOrEmpty(e.Text) || _processExitHandled != 0)
            {
                Debug.WriteLine($"[TerminalView] OnTextInput: No PTY or empty text");
                base.OnTextInput(e);
                return;
            }

            // In Win32 input mode ordinary keys are already reported as records from KeyDown, so
            // sending their text again here would double every keystroke -- which is what the blanket
            // skip was protecting against.
            //
            // But not everything that reaches TextInput has a KeyDown behind it. An IME commits its
            // composition here, and so does a dead-key sequence: two presses that produce one
            // character, and the character arrives as text with no key event carrying it. Those were
            // silently discarded, so under cmd.exe no CJK, no accented Latin, nothing composed at all
            // could be typed.
            //
            // Composed text is sent as records of its own, one per character, which is what the
            // process is reading.
            if (_terminal.Win32InputMode)
            {
                // Was a record already sent for this keystroke? Then this is the same character
                // arriving a second way and must be dropped. Nothing sent means nothing produced it
                // -- an IME commit, or the second press of a dead-key pair -- and that is the text
                // this branch exists to carry.
                var alreadySent = _win32RecordSentForThisStroke;
                _win32RecordSentForThisStroke = false;
                // Either branch consumes this event: it is duplicate text already represented by
                // KeyDown, or it is composed text that this control sends as VK_PACKET records.
                e.Handled = true;
                if (alreadySent)
                    return;
                await SendToPtyAsync(Win32TextRecords(e.Text!)).ConfigureAwait(false);
                return;
            }

            // Typing over a selection replaces it; failing that, the selection is simply dropped. The
            // anchor goes either way — see OnKeyDown.
            NoteInputStart();

            var replaceKeys = _pendingReplaceKeys.Length > 0 ? _pendingReplaceKeys : TakeKeyboardSelectionDeletion();
            _pendingReplaceKeys = string.Empty;
            if (replaceKeys.Length == 0)
            {
                _kbSelAnchor = null;
                _kbSelWholeInput = false;
                if (_terminal.Selection.HasSelection)
                {
                    _terminal.Selection.ClearSelection();
                    RequestPaint();
                }
            }

            FollowTail();   // typing returns the view to the prompt

            try
            {
                Debug.WriteLine($"[TerminalView] OnTextInput: Sending '{e.Text}' to PTY");

                // Before the await, for the reason given on the key-up path: this handler is async
                // void, so it returns to the routing at the await and the event goes on bubbling
                // while still marked unhandled. Found by review of that other site and fixed here
                // too rather than left as its twin.
                e.Handled = true;
                await SendToPtyAsync(replaceKeys + e.Text).ConfigureAwait(false);
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"[{_instanceId}] Error handling text input: {ex.Message}");
            }
        }

        private void OnTerminalBufferChanged(object? sender, XT.Events.TerminalEvents.BufferChangedEventArgs e)
        {
            Dispatcher.UIThread.Post(() =>
            {
                var oldValue = _isAlternateBuffer;
                _isAlternateBuffer = e.Buffer == XT.Common.BufferType.Alternate;

                if (oldValue != _isAlternateBuffer)
                {
                    // A selection belongs to the screen it was made on. The two buffers are different
                    // content at the same coordinates, so a selection left standing across the switch
                    // still highlights rows 3 to 7 -- of whatever is there NOW. Copying it returned
                    // the text of a full-screen application the user had never selected, from a
                    // rectangle that looked like it was over their shell output.
                    //
                    // Cleared on the switch either way, since it is wrong in both directions.
                    if (_terminal.Selection.HasSelection)
                        _terminal.Selection.ClearSelection();

                    // With the keyboard-selection anchor, which is in the same coordinates and would
                    // otherwise go on extending a selection that no longer exists.
                    _kbSelAnchor = null;
                    _kbSelWholeInput = false;

                    // And any drag in flight. The pointer is still down, but what it was dragging
                    // over is gone.
                    _isSelecting = false;
                    _pendingSelectionStart = null;
                    _lastReportedMotion = null;

                    RaisePropertyChanged(IsAlternateBufferProperty, oldValue, _isAlternateBuffer);
                }

                RaisePropertyChanged(MaxScrollbackProperty, default(int), MaxScrollback);
                RaisePropertyChanged(ViewportLinesProperty, default(int), ViewportLines);
                RaisePropertyChanged(ViewportYProperty, default(int), ViewportY);
                RequestPaint();
            });
        }

        private void OnTerminalCursorStyleChanged(object? sender, XT.Events.TerminalEvents.CursorStyleChangedEventArgs e)
        {
            Dispatcher.UIThread.Post(() =>
            {
                if (!Equals(CursorStyle, e.Style))
                {
                    SetValue(CursorStyleProperty, e.Style);
                }

                if (!Equals(CursorBlink, e.Blink))
                {
                    SetValue(CursorBlinkProperty, e.Blink);
                }

                RequestPaint();
            });
        }

        /// <summary>How long the reader waits for the UI thread to answer a window query.</summary>
        /// <remarks>
        /// Generous for a handler that only reads window state, and short enough that a wedged UI
        /// thread costs a pause rather than the session. See <see cref="OnTerminalWindowInfoRequested"/>.
        /// </remarks>
        private static readonly TimeSpan WindowInfoPatience = TimeSpan.FromMilliseconds(250);

        private async void OnTerminalDataReceived(object? sender, XT.Events.TerminalEvents.DataEventArgs e)
        {
            // Terminal wants to send data (typically in response to device status queries, etc.)
            await SendToPtyAsync(e.Data).ConfigureAwait(false);
        }

        private readonly SemaphoreSlim _semaphore = new SemaphoreSlim(1, 1);

        /// <summary>
        /// The keys currently held down, so a second key-down for one of them can be reported as a
        /// REPEAT rather than a second press.
        /// </summary>
        /// <remarks>
        /// Avalonia's KeyEventArgs carries no repeat flag, and the protocol distinguishes the two --
        /// an application that negotiated event types asked to be able to tell them apart, and
        /// giving it a press for every auto-repeat answers a question it did not ask. Keyed on the
        /// physical key AND the logical one, because an unrecognised key reports PhysicalKey.None
        /// and several different keys would otherwise share the one entry.
        /// </remarks>
        private readonly HashSet<(PhysicalKey Physical, Key Logical)> _keysHeld = new();

        /// <summary>
        /// Whether the Win32 path has already reported the keystroke now in flight.
        /// </summary>
        /// <remarks>
        /// Set when a key produces an INPUT_RECORD and read by the TextInput that may follow it, so
        /// an ordinary key is not sent twice while composed text -- which has no key event behind it
        /// -- still gets through. Cleared as it is read: it describes one keystroke, not a mode.
        /// </remarks>
        private bool _win32RecordSentForThisStroke;

        /// <summary>
        /// A url currently under the pointer, resolved to the buffer cells it occupies.
        /// A url that wrapped across the right edge covers more than one segment.
        /// </summary>
        internal sealed class HoveredUrl
        {
            public HoveredUrl(string url, List<(int Line, int StartCol, int EndCol)> segments,
                              bool fromSequence = false)
            {
                Url = url;
                Segments = segments;
                FromSequence = fromSequence;
            }

            public string Url { get; }

            /// <summary>
            /// Whether the program declared this link with OSC 8, rather than the text merely looking
            /// like a URL.
            /// </summary>
            /// <remarks>
            /// Surfaced to the host because the two deserve different trust. A declared link is a
            /// statement of intent from the program; a matched one is a guess about characters that
            /// happened to be on screen, and its target is whatever the user can already read.
            /// </remarks>
            public bool FromSequence { get; }

            /// <summary>Inclusive cell ranges, one per buffer line the url spans.</summary>
            public List<(int Line, int StartCol, int EndCol)> Segments { get; }

            public bool Contains(int line, int col)
            {
                foreach (var s in Segments)
                {
                    if (s.Line == line && col >= s.StartCol && col <= s.EndCol)
                        return true;
                }
                return false;
            }

            public bool SameAs(HoveredUrl? other)
                => other != null &&
                   Url == other.Url &&
                   other.Segments.Count == Segments.Count &&
                   other.Segments[0] == Segments[0];
        }

        private static int CountChar(string text, char c)
        {
            int count = 0;
            foreach (var ch in text)
            {
                if (ch == c)
                    count++;
            }
            return count;
        }

        /// <summary>The most recent shape a program asked for; only the last one is applied.</summary>
        /// <remarks>
        /// Written on the pty reader thread and read on the UI thread, so the accesses are volatile:
        /// without that "last one wins" is a claim the memory model does not actually make, and the
        /// UI thread could apply a shape two changes stale.
        /// </remarks>
        private volatile string? _pendingPointerShape;

        /// <summary>Whether a shape change is already waiting to be applied.</summary>
        /// <remarks>Guarded by the queue's own lock, like the palette walk.</remarks>
        private bool _pointerShapeQueued;

        /// <summary>Host callbacks waiting for the UI thread, and whether a drain is already queued.</summary>
        private readonly List<Action> _pendingHostCallbacks = new();
        private bool _hostDrainQueued;

        /// <summary>
        /// Runs <paramref name="callback"/> on the UI thread, sharing ONE dispatcher job with
        /// everything else queued before the UI thread gets round to it.
        /// </summary>
        /// <remarks>
        /// <para>These seams are raised from Terminal.Write on the pty reader thread, once per escape
        /// sequence, and posting each one separately means a burst of sequences becomes a burst of
        /// dispatcher entries -- each holding a closure, which holds its event args, which holds
        /// whatever they carry. Measured: 0.9 MB of output pinning 86 MB of live heap, because the
        /// reader can queue far faster than the UI thread drains.</para>
        /// <para>Nothing is dropped. The callbacks still run, in order, and each still does exactly
        /// what it did -- what changes is that N of them cost one dispatcher job instead of N, and
        /// live in a list rather than N captured closures.</para>
        /// <para>The flag is what makes it one job: a drain is queued only when none is pending, and
        /// the next arrival joins the queue the pending one will read.</para>
        /// </remarks>
        private void PostToHost(Action callback)
        {
            bool needsDrain;
            lock (_pendingHostCallbacks)
            {
                _pendingHostCallbacks.Add(callback);
                needsDrain = !_hostDrainQueued;
                _hostDrainQueued = true;
            }

            if (needsDrain)
                Dispatcher.UIThread.Post(DrainHostCallbacks);
        }

        private void DrainHostCallbacks()
        {
            Action[] batch;
            lock (_pendingHostCallbacks)
            {
                batch = _pendingHostCallbacks.ToArray();
                _pendingHostCallbacks.Clear();
                _hostDrainQueued = false;
            }

            foreach (var callback in batch)
            {
                // One failing callback must not swallow the rest of the batch. Separately posted,
                // each of these was independent; batching them must not make them share a fate.
                // The WHOLE exception, not just its message. A message alone drops the stack and any
                // inner exception, which is most of what makes a swallowed failure diagnosable --
                // and swallowing is the point here, so this line is all anybody gets.
                try { callback(); }
                catch (Exception ex) { Debug.WriteLine($"[TerminalView] host callback failed: {ex}"); }
            }
        }

        /// <summary>
        /// The clipboard writes still to happen, chained so each waits for the one before it.
        /// </summary>
        /// <remarks>
        /// A Task chain rather than a semaphore. SemaphoreSlim does not promise FIFO fairness -- it
        /// releases A waiter, not the LONGEST-waiting one -- so under contention two queued writes
        /// could still resume out of order, which is the very thing the gate was added to prevent.
        /// A chain has the ordering in its shape: each write is appended to the tail, so it cannot
        /// begin until its predecessor has finished.
        ///
        /// Only ever touched on the UI thread, which is where the posts land, so the field needs no
        /// lock of its own.
        /// </remarks>
        private Task _clipboardWrites = Task.CompletedTask;

        /// <summary>The one mime a platform clipboard can be relied on to hold.</summary>
        private const string SupportedClipboardMime = "text/plain";

        /// <summary>The running read loop, so a detach can wait for a cancellable one to finish.</summary>
        private Task? _readLoopTask;

        /// <summary>True while the connection belongs to an outside owner — see <see cref="AttachConnection"/>.</summary>
        private bool _externalConnection;

        /// <summary>
        /// True while a PTY is attached and its process has not been reported as exited. A view that has never
        /// launched, or whose process has ended, is false.
        /// </summary>
        /// <remarks>
        /// A host that shows a terminal only once there is something to show needs to ask this — the alternative
        /// is tracking it in parallel from <see cref="ProcessExited"/> and guessing at the starting state.
        /// </remarks>
        public bool IsLive
        {
            get
            {
                // Under the gate, because the two halves only mean anything together. InstallConnection
                // publishes the connection and resets the interlock as one step; reading them outside can
                // catch the new connection paired with the old flag for a moment after an attach, and report
                // a freshly attached PTY as not live.
                lock (_exitGate)
                {
                    return _ptyConnection != null && Volatile.Read(ref _processExitHandled) == 0;
                }
            }
        }

        /// <summary>
        /// One cell's width at the current font — text is drawn at <c>col * CharWidth</c>. A host overlay
        /// can size its stand-in caret from this so waking the session shifts nothing.
        /// </summary>
        public double CharWidth
        {
            get { if (_charWidth <= 0) UpdateTextMetrics(); return _charWidth; }
        }

        /// <summary>
        /// One row's height at the current font — row N's text top-left is <c>(0, N * CharHeight)</c>,
        /// so a stand-in prompt lands on the live first row by placing it at the view's own origin.
        /// </summary>
        public double CharHeight
        {
            get { if (_charHeight <= 0) UpdateTextMetrics(); return _charHeight; }
        }

        /// <summary>
        /// Force a correct full re-render. Upstream's first paint is focus-gated (the blink/redraw loop only runs
        /// when focused) and frame-throttled, so a freshly-launched or just-shown terminal can stay blank until
        /// clicked. This re-applies font metrics, re-grids to the current size, drops the per-line render caches,
        /// and invalidates immediately (bypassing <see cref="TerminalRenderThrottle"/>). Safe to call any time
        /// (no-op-ish before the terminal is initialised).
        /// </summary>
        public void Refresh()
        {
            if (_terminal == null)
                return;

            UpdateTextMetrics();

            // Drop cached text runs so each line rebuilds at the current metrics/size.
            for (int y = 0; y < _terminal.Buffer.Length; y++)
            {
                var line = _terminal.Buffer.GetLine(y);
                if (line != null)
                    line.Cache = null;
            }

            // Re-run layout (ArrangeOverride re-grids the terminal + PTY for the current size), then paint now.
            InvalidateMeasure();
            InvalidateArrange();
            InvalidateVisual();
        }

        protected override Size ArrangeOverride(Size finalSize)
        {
            // Calculate how many columns fit in the allocated width
            if (_charWidth > 0)
            {
                // The gutter is taken out of the width before columns are counted, so turning one on
                // narrows the terminal rather than pushing text off the right-hand edge. Clamped the
                // same way Render and PointerColumn clamp it -- a negative width must not mint columns.
                int newCols = Math.Max(1, (int)((finalSize.Width - Math.Max(0, GutterWidth)) / _charWidth));

                // The status row comes off the height the way the gutter comes off the width: before
                // anything is counted, so the grid never contains it. An application told it has 24
                // rows must have 24 rows it can actually write to -- a status line carved out of the
                // grid afterwards would leave it addressing a row that is not there.
                int newRows = Math.Max(1, (int)((finalSize.Height - StatusLineHeight) / _charHeight));

                // Only resize if dimensions have changed
                if (newCols != _terminal.Cols || newRows != _terminal.Rows)
                {
                    // Under the lock, like every other mutation of the emulator. A resize reflows the
                    // whole buffer, and the pty reader can be inside Terminal.Write at the same
                    // moment -- one thread rewriting the lines another is appending to. Layout runs
                    // on the UI thread and output arrives on the reader thread, so the two meet
                    // whenever a window is resized while anything is printing.
                    lock (_terminalLock)
                    {
                        // Marked as OURS for the duration. Terminal.Resize raises Resized
                        // synchronously, and OnTerminalResized answers a program's resize by asking
                        // the host for a new window size -- which is right for DECCOLM and wrong
                        // here, where the grid was derived FROM the window size a moment ago.
                        // Without the flag every drag of the window edge would bounce back as a
                        // request to snap the window to an exact multiple of the cell.
                        _regridFromLayout = true;
                        try
                        {
                            _terminal.Resize(newCols, newRows);
                        }
                        finally
                        {
                            _regridFromLayout = false;
                        }
                    }

                    // Outside it: this is a write to the pty, which has its own serialisation, and
                    // holding the terminal lock across a call into the platform would block the
                    // reader for no reason.
                    _ptyConnection?.Resize(newCols, newRows);

                    RaisePropertyChanged(ViewportLinesProperty, default(int), ViewportLines);
                }
            }

            return finalSize;
        }


        /// <summary>
        /// One OSC 66 block waiting for the deferred pass: which line, which cells, and where the
        /// anchor row landed on screen. Deferred because a block taller than one row must paint
        /// AFTER every row's background — rows render top to bottom, and the row below an anchor
        /// would otherwise fill straight over the glyph's lower half.
        /// </summary>
        private readonly record struct SizedBlockDraw(
            XT.Buffer.BufferLine Line, XT.Buffer.LineSizedRun Run, double StartYPos, double RowHeight);

        private readonly List<SizedBlockDraw> _sizedBlockDraws = new();

        /// <summary>
        /// Reads one row into runs. Reads ONLY -- see <see cref="CollectLineRuns"/> for why nothing here
        /// may paint or publish.
        /// </summary>
        private List<CachedTextRun> BuildLineRuns(BufferLine line, double startYPos, double rowHeight,
                                                  out bool hasSizedRuns)
        {
            var textRuns = new List<CachedTextRun>();

            // The line's own runs, back to front. Every picture on the line is already one run per
            // line, so there is nothing to collect and nothing to coalesce -- the emulator's storage
            // is the draw list, and each run is a single blit.
            //
            // Runs are drawn in the order they are added, so appending the ones behind the text,
            // then the text, then the ones in front is what makes the layers composite: a
            // translucent picture blends over whatever was drawn under it.
            var placements = OrderedPlacements(line);
            var nextPlacement = 0;

            // Allocated only when there IS a picture on the line, which for almost every line there
            // is not. An empty list per line per rebuild is one allocation per row per frame to hold
            // nothing. The shared empty instance is never written to -- the loop below only adds to
            // it after OrderedPlacements has returned something.
            var painted = placements.Count > 0 ? new List<XT.Graphics.LinePlacement>(placements.Count) : EmptyPlacements;

            for (; nextPlacement < placements.Count && placements[nextPlacement].ZIndex < 0; nextPlacement++)
            {
                AppendImageRun(line, placements[nextPlacement], textRuns, painted);
                painted.Add(placements[nextPlacement]);
            }

            // A line holding OSC 66 blocks is drawn in two stages: everything OUTSIDE the
            // blocks now, the blocks themselves in the deferred pass after every row — a block
            // taller than one row must not be painted over by the next row's background. The
            // anchor cell's Width spans the whole block, so drawing it as a normal run would put
            // the text at base size in a corner of the box. Sized lines are not cached: the
            // cache stores finished draw calls, and the blocks are deliberately NOT drawn here.
            hasSizedRuns = line.HasSizedRuns;

            for (int x = 0; x < _terminal.Cols;)
            {
                if (x >= line.Length)
                    break;

                if (hasSizedRuns && line.TryGetSizedRunAt(x, out var sizedRun) && sizedRun.Covers(x))
                {
                    _sizedBlockDraws.Add(new SizedBlockDraw(line, sizedRun, startYPos, rowHeight));
                    x = sizedRun.EndColumn;
                    continue;
                }

                var cell = line[x];
                string text = String.Empty;
                int cellCount = 0;
                int runStartX = 0;
                var runHasBackdrop = CoveredByBackdrop(painted, x, x + Math.Max(1, cell.Width));

                // Nothing is drawn where a Sixel covers, because a Sixel REPLACED what was there.
                if (CoveredBySixel(line, x))
                {
                    x++;
                    continue;
                }

                // Skip width-0 cells. There are TWO kinds, and only one of them is a placeholder.
                //
                // The placeholder behind a wide glyph carries no content, and skipping it is what stops the
                // glyph being drawn twice. The other kind is a combining character that had nothing in front
                // of it to combine with — a line beginning with U+0301, a stray variation selector, a keycap
                // with no digit — which the emulator stores in a cell of its own after
                // TryAppendToPreviousCell finds no base. That one DOES carry content, and skipping it is
                // also right: a combining mark with nothing to combine with has nothing to draw.
                //
                // This used to assert the content was empty, on the assumption that a placeholder was the
                // only way to reach here. It is not, so the assert fired on ordinary output — printing a
                // lone combining acute is enough — and cost a debugging session before anyone questioned
                // the premise rather than the buffer.
                if (cell.Width == 0)
                {
                    x++;
                    continue;
                }
                else if (cell.Width == 1)
                {
                    // Collect consecutive cells with same attributes.
                    //
                    // The builder is REUSED, not allocated per run. This is the innermost loop of the
                    // renderer -- a screen of text is a few hundred runs and every one of them was
                    // allocating a builder plus its backing array, to be thrown away a line later.
                    // Cleared rather than replaced, so the array it grew to survives with it.
                    var textBuilder = _runTextBuilder;
                    textBuilder.Clear();
                    cellCount = 0;  // Total cell positions consumed (including wide char placeholders)
                    runStartX = x;
                    while (x < line.Length && x < _terminal.Cols)
                    {
                        var currentCell = line[x];

                        // Stop if we hit a different attribute or a placeholder cell mid-run.
                        //
                        // A KITTY picture is no reason to stop: it is an overlay, the cell under it
                        // still carries whatever was printed there, and the z-index decides which of
                        // them a viewer sees. A SIXEL is not -- see CoveredBySixel.
                        //
                        // An OSC 66 block is a boundary too, and nothing here would otherwise notice
                        // one. A fractional block is always s=1, so its cells are a single column wide
                        // and carry the SGR that was in force when it was printed; without this,
                        // preceding text with the same attributes swallows the whole run and draws it
                        // at base size, because the outer loop only looks for a run on the column it
                        // starts an iteration on.
                        if (currentCell.Width != 1 || currentCell.Attributes != cell.Attributes
                            || CoveredBySixel(line, x)
                            // Background fill is cached for the whole text run. Split where backdrop
                            // coverage changes so suppressing that fill affects only columns with a
                            // negative-z picture behind them, not every same-style cell beside it.
                            || CoveredByBackdrop(painted, x, x + 1) != runHasBackdrop
                            || (hasSizedRuns && line.TryGetSizedRunAt(x, out _)))
                            break;
                        // Append the CHARACTER, not the Content string, whenever the cell is a single
                        // codepoint in the basic plane -- which is nearly every cell of nearly every
                        // terminal. Content is derived: it looks the codepoint up in an intern table
                        // and hands back a string, and Append then copies its one char out again.
                        // Going straight to the char skips the lookup and the string entirely.
                        //
                        // Anything else -- a cluster, an astral codepoint -- still goes through
                        // Content, which is the only thing that knows how to spell it.
                        // ClusterId 0 is "no cluster" -- XTerm.NET's ClusterTable.None, which is
                        // internal to it, so the value is spelled out with the reason rather than
                        // referenced. A cell with a cluster spans several codepoints and only
                        // Content can spell it.
                        if (currentCell.ClusterId == 0
                            && currentCell.CodePoint > 0 && currentCell.CodePoint < 0x10000)
                            textBuilder.Append((char)currentCell.CodePoint);
                        else
                            textBuilder.Append(currentCell.Content);

                        cellCount += currentCell.Width;

                        // Skip the placeholder cell that follows a wide character
                        x += currentCell.Width;
                    }
                    text = textBuilder.ToString();
                }
                else if (cell.Width == 2)
                {
                    text = cell.Content;
                    cellCount = cell.Width;
                    runStartX = x;
                    x += cell.Width;  // Move past wide character and its placeholder
                }

                // A ZWJ sequence spans several cells with the joiner tacked onto all but the last, so the run
                // collected above can be only the first component of one glyph. Pull in the rest before
                // shaping — otherwise HarfBuzz never sees the cluster and a family emoji draws as separate
                // people. Applies to both branches: ❤️‍🔥 starts in a width-1 cell and continues into a wide one.
                text = GraphemeRuns.AbsorbJoinedCells(line, _terminal.Cols, cell, text, ref x, ref cellCount);

                var background = cell.GetBackgroundBrush(_palette, this.Background);
                var foreground = cell.GetForegroundBrush(_palette, this.Foreground, _boldIsBright);
                // Apply cell-level inverse attribute
                // Whether this run ends up drawn with the colours swapped. Once they are, the fill is no
                // longer optional: the "background" being painted is the text colour.
                bool swapped = false;
                if (cell.Attributes.IsInverse())
                    (foreground, background, swapped) = (background, foreground, !swapped);
                // Apply terminal-wide reverse video mode (DECSCNM)
                if (_terminal.ReverseVideo)
                    (foreground, background, swapped) = (background, foreground, !swapped);

                // Options.MinimumContrastRatio. Applied AFTER the swaps, because the pair being
                // tested must be the pair being painted -- an inverted cell's readable colour is its
                // swapped one -- and BEFORE conceal, which makes the foreground transparent on
                // purpose and must stay the last word. Only the foreground moves; the background is
                // the theme's.
                //
                // `background` here is the right thing to test against even when no fill is painted:
                // GetBackgroundBrush resolves a default-background cell to the same colour Render
                // painted the surface with. The guards skip the cases where "the colour behind this
                // text" has no single answer -- a run over an image placement, a translucent host
                // background showing through, or a non-solid brush -- and the runs xterm.js also
                // exempts because their glyphs join into shapes with their neighbours.
                if (_minimumContrast.Active
                    && !runHasBackdrop
                    && !MinimumContrast.IsExemptRun(text)
                    && foreground is ISolidColorBrush fgSolid
                    && background is ISolidColorBrush bgSolid
                    && BufferCellExtensions.IsFullyOpaque(background))
                {
                    var contrasted = _minimumContrast.Apply(fgSolid.Color, bgSolid.Color);
                    if (contrasted != fgSolid.Color)
                        foreground = new SolidColorBrush(contrasted, fgSolid.Opacity);
                }

                // SGR 8. The emulator has recorded it since the parser was written and nothing here
                // ever read it, so concealed text -- a password prompt that echoes, a spoiler --
                // was drawn in full.
                //
                // Applied AFTER the swaps above -- see ApplyConceal, where the ordering is the
                // substance of it rather than a detail.
                foreground = cell.ApplyConceal(foreground);
                foreground = cell.ApplyBlinkPhase(foreground, this._cursorBlinkOn);

                var style = cell.GetFontStyle();
                var weight = cell.GetFontWeight();
                var td = cell.GetTextDecorations();

                // Underlines are drawn by hand below rather than through TextDecorations, because
                // Avalonia has no curly decoration and SGR 58 gives the underline a colour of its own.
                // Decided BEFORE shaping, because whether a blank run needs shaping at all depends on it.
                var underlineStyle = cell.Attributes.GetUnderlineStyle();
                IBrush? underlineBrush = null;
                if (underlineStyle != XT.Common.UnderlineStyle.None)
                {
                    underlineBrush = cell.GetUnderlineColor(_palette) is { } uc
                        ? new ImmutableSolidColorBrush(uc)
                        : foreground;

                    // Through the blink phase like the glyph. An underline WITHOUT SGR 58 borrows
                    // the foreground and inherits its transparency for free; one WITH its own
                    // colour resolved opaque here and stayed lit through the off half -- blinking
                    // text under a steady underline, on the classic path only, while the Skia
                    // renderer suppressed both together.
                    underlineBrush = cell.ApplyBlinkPhase(underlineBrush, this._cursorBlinkOn);
                }

                // A run of blanks with no decoration has nothing to draw. Most of a terminal is exactly
                // that -- the grid is blank to the right of every line -- and each of those runs was
                // shaping a string of spaces and issuing a DrawText for it. Spaces have no ink, so the
                // call could only ever produce nothing.
                //
                // Carried by giving the run NO FormattedText rather than by a test at the draw call: the
                // string is then never shaped either, and because the draw path already skips a run with
                // no text the saving holds for every later frame the row is replayed from the cache. It
                // did not before -- the skip lived on the build path, so a blank run was skipped on the
                // frame it was built and drawn on all the rest.
                //
                // The DECORATION check is what makes it safe: an underline or a strikethrough on blanks
                // is visible, and an underline is drawn by hand rather than by DrawText. A fill is safe
                // too -- it is a run of its own business, drawn whether or not there is text, which is
                // why swapped runs and coloured backgrounds are unaffected.
                // The fast path first: shape once here rather than on every frame that replays
                // the line. Declines anything it cannot draw faithfully -- see TryBuildGlyphRun --
                // and a decoration is one of those, because that is set on the FormattedText.
                GlyphRun? glyphs = null;
                FormattedText? formattedText = null;
                if (!IsBlankRun(text) || underlineStyle != XT.Common.UnderlineStyle.None || td != null)
                {
                    // A run the ligature switch cares about must reach the shaper, which the
                    // fast path never does -- it maps characters to glyphs one for one.
                    glyphs = td == null && !LigaturesWantShaping(text, style, weight)
                        ? TryBuildGlyphRun(text, cellCount, style, weight) : null;
                    if (glyphs is null)
                    {
                        var typeface = new Typeface(FontFamily, style, weight);
                        formattedText = new FormattedText(text, CultureInfo.CurrentCulture, FlowDirection.LeftToRight,
                                                          typeface, FontSize, foreground);
                        ApplyLigatureSetting(formattedText);
                        if (td != null)
                            formattedText.SetTextDecorations(td);
                    }
                }

                // A cell that carries no background of its own and was not swapped paints nothing, leaving
                // whatever the view is layered over to show through.
                //
                // Under DECSCNM it has to paint anyway. "Not swapped" there means the cell inverted
                // and the screen inverted, cancelling -- so its background is the ordinary default
                // while the SURFACE is the inverted one, and the two are no longer the same colour.
                // Leaving it unpainted drew a negative cell's text in the normal foreground on an
                // inverted sheet: white on white, and vttest's four `negative` rows vanished from
                // the light-background pattern.
                var fill = swapped || _terminal.ReverseVideo || cell.GetBackgroundColor(_palette).HasValue
                    ? background
                    : null;

                // Unless a picture is already there. Placements with a NEGATIVE z-index are drawn
                // before the text precisely so the text sits on top of them -- and then every cell
                // with a background of its own painted an opaque rectangle over the picture it was
                // supposed to be sitting on, erasing the thing the z-index asked for.
                //
                // The text still draws. What is dropped is only the fill, which is what was covering
                // the picture; a cell with no picture behind it is untouched.
                if (fill is not null && runHasBackdrop)
                    fill = null;
                // Cache only content-dependent data, not screen position
                // Named rather than positional: the record gained Placement and Image ahead of these
                // when pictures moved onto lines, so position no longer says which is which.
                var run = new CachedTextRun(formattedText, runStartX, cellCount, fill,
                                            Glyphs: glyphs, Foreground: foreground,
                                            UnderlineStyle: underlineStyle, UnderlineBrush: underlineBrush);
                textRuns.Add(run);


            }

            // And the pictures that cover the text, still back to front, now that it is down.
            for (; nextPlacement < placements.Count; nextPlacement++)
            {
                AppendImageRun(line, placements[nextPlacement], textRuns, painted);
                painted.Add(placements[nextPlacement]);
            }
            return textRuns;
        }

        private static readonly List<XT.Graphics.LinePlacement> EmptyPlacements = new();

        /// <summary>
        /// Where the caret is drawn: its column, and its ABSOLUTE row (<c>YBase + Y</c> space, the same one
        /// the viewport check uses).
        /// </summary>
        /// <remarks>
        /// <para>Normally the shell's cursor. While a keyboard selection is in flight it follows the
        /// selection's moving EDGE instead, the way it does in every text field — extending a selection and
        /// leaving the caret behind reads as a stuck cursor.</para>
        /// <para>Only where the caret is DRAWN changes. The shell still owns the real cursor and is never
        /// told about this, because it must not be: the buffer position is where the shell will write next,
        /// and moving it to follow a selection would put the next output in the wrong place.</para>
        /// <para>Internal rather than private so this is directly assertable. It is otherwise only
        /// observable as pixels, and the test suite runs on the headless drawing backend.</para>
        /// </remarks>
        /// <summary>
        /// True while the caret should not be drawn at all, because there is no one place it belongs.
        /// </summary>
        /// <remarks>
        /// Select-all leaves the caret indeterminate: the whole input is selected, so neither end is more
        /// the cursor than the other. Drawing it at one of them reads as though only that end were live.
        /// Editors hide it; so does this. Steering an edge with Shift+arrow makes it meaningful again.
        /// </remarks>
        internal bool CaretHidden => _kbSelWholeInput && _terminal.Selection.HasSelection;

        internal (int Column, int AbsoluteRow) CaretPosition
        {
            get
            {
                // Both conditions: the anchor says a gesture is in flight, the selection says it still has
                // something to show. Belt and braces — every path that clears one now clears the other, but
                // a stale anchor pins the caret while the shell's cursor moves on, which is the exact
                // failure this branch has already hit twice.
                if (_kbSelAnchor is not null && _terminal.Selection.HasSelection)
                {
                    int cols = Math.Max(1, _terminal.Cols);
                    return (_kbSelFocus % cols, _terminal.Buffer.ViewportY + (_kbSelFocus / cols));
                }

                return (_terminal.Buffer.X, _terminal.Buffer.YBase + _terminal.Buffer.Y);
            }
        }

        /// <summary>VK_PACKET — "the unicode field is the whole of this event".</summary>
        private const int VirtualKeyPacket = 0xE7;

        private const int VirtualKeyCapital = 0x14;
        private const int VirtualKeyNumLock = 0x90;
        private const int VirtualKeyScroll = 0x91;



        /// <summary>
        /// Implements Avalonia's <see cref="TextInputMethodClient"/> for the terminal.
        /// This enables IME (Input Method Editor) support so that non-English characters
        /// can be composed correctly with the composition window positioned at the cursor.
        /// </summary>
        private sealed class TerminalInputMethodClient : TextInputMethodClient
        {
            private readonly TerminalView _view;
            private string? _preeditText;

            public TerminalInputMethodClient(TerminalView view)
            {
                _view = view;
            }

            /// <summary>
            /// Gets the preedit (composition) text currently being entered by the IME.
            /// </summary>
            public string? PreeditText => _preeditText;

            /// <summary>
            /// The visual that is rendering the text — this is the terminal view itself.
            /// </summary>
            public override Visual TextViewVisual => _view;

            /// <summary>
            /// Indicates the terminal supports displaying uncommitted preedit text.
            /// </summary>
            public override bool SupportsPreedit => true;

            /// <summary>
            /// Indicates the terminal can provide surrounding text for IME context.
            /// </summary>
            public override bool SupportsSurroundingText => true;

            /// <summary>
            /// Returns the text content of the current line up to the cursor,
            /// providing context for the IME.
            /// </summary>
            public override string SurroundingText => LineAndCaret().Text;

            /// <summary>
            /// The cursor's line as one string, and where the caret sits INSIDE that string.
            /// </summary>
            /// <remarks>
            /// <para>Both in one pass, because they have to agree and they did not. The text was
            /// built a cell at a time while the caret was reported as a COLUMN, and the two index
            /// spaces are only the same while every cell holds exactly one char. A grapheme cluster
            /// does not: an e with a combining acute is one cell and two chars, so from the first one
            /// on the line the IME was told the caret was somewhere it was not -- and an IME uses
            /// exactly this to decide what it is composing over.</para>
            /// <para>Counting the offset in the same loop that appends makes them agree by
            /// construction rather than by both being derived carefully.</para>
            /// </remarks>
            private (string Text, int Caret) LineAndCaret()
            {
                try
                {
                    var buffer = _view._terminal.Buffer;
                    int absoluteY = buffer.YBase + buffer.Y;
                    var line = buffer.GetLine(absoluteY);
                    if (line == null) return (string.Empty, 0);

                    var cursorColumn = buffer.X;
                    var sb = new StringBuilder();
                    var caret = 0;

                    for (int x = 0; x < line.Length; x++)
                    {
                        // Taken before appending, so a caret AT this column is the offset in front of
                        // whatever this cell contributes.
                        if (x == cursorColumn)
                            caret = sb.Length;

                        var cell = line[x];
                        // Width-zero cells are the continuation half of a wide glyph. They occupy a
                        // terminal column but contribute no text, so inserting a space here shifts
                        // every subsequent IME offset. Preserve content only for the defensive case
                        // of an independently populated zero-width cell.
                        if (cell.Width == 0)
                        {
                            if (!string.IsNullOrEmpty(cell.Content))
                                sb.Append(cell.Content);
                        }
                        else
                        {
                            sb.Append(string.IsNullOrEmpty(cell.Content) ? " " : cell.Content);
                        }
                    }

                    // A caret past the last cell is the end of the text, which is where it sits while
                    // typing at the end of a line -- the common case.
                    if (cursorColumn >= line.Length)
                        caret = sb.Length;

                    return (sb.ToString(), caret);
                }
                catch
                {
                    return (string.Empty, 0);
                }
            }

            /// <summary>
            /// Gets the cursor rectangle relative to the terminal view,
            /// used to position the IME composition window at the cursor.
            /// </summary>
            public override Rect CursorRectangle
            {
                get
                {
                    try
                    {
                        var buffer = _view._terminal.Buffer;
                        int cursorX = buffer.X;
                        int absoluteCursorY = buffer.YBase + buffer.Y;
                        int viewportY = buffer.ViewportY;
                        int screenY = absoluteCursorY - viewportY;

                        // The gutter, the third place the offset is needed. This rectangle is in the
                        // control's space, which is the space the render translates the grid within --
                        // without it the composition window sits GutterWidth px to the left of the
                        // caret it is meant to be under, for the whole session. Clamped the way
                        // PointerColumn and ArrangeOverride clamp it.
                        double posX = cursorX * _view._charWidth + Math.Max(0, _view.GutterWidth);
                        double posY = screenY * _view._charHeight;

                        return new Rect(posX, posY, _view._charWidth, _view._charHeight);
                    }
                    catch
                    {
                        return default;
                    }
                }
            }

            /// <summary>
            /// Gets or sets the selection range within the surrounding text.
            /// For a terminal, this corresponds to the cursor column position.
            /// </summary>
            public override TextSelection Selection
            {
                get
                {
                    // Into SurroundingText's index space, not the column space it used to report.
                    var caret = LineAndCaret().Caret;
                    return new TextSelection(caret, caret);
                }
                set { /* Terminal selection is managed separately */ }
            }

            /// <summary>
            /// Called by the IME to display uncommitted composition text at the cursor position.
            /// </summary>
            public override void SetPreeditText(string? preeditText)
            {
                _preeditText = preeditText;
                _view.RequestInvalidate();
            }

            /// <summary>
            /// Called by the IME to display uncommitted composition text with an optional
            /// cursor offset within the preedit string.
            /// </summary>
            /// <param name="preeditText">The current composition text, or null/empty to clear it.</param>
            /// <param name="cursorPos">The cursor position within the preedit string.
            /// A terminal renders preedit as a simple underlined overlay so the within-composition
            /// cursor position is not used here.</param>
            public override void SetPreeditText(string? preeditText, int? cursorPos)
            {
                // cursorPos (position of IME cursor within the composition string) is intentionally
                // not used: the terminal renders preedit as a simple underlined text overlay and
                // does not support a separate cursor inside the composition window.
                _preeditText = preeditText;
                _view.RequestInvalidate();
            }

            /// <summary>
            /// Clears any active preedit text (e.g. when focus is lost).
            /// </summary>
            public void ClearPreeditText()
            {
                if (_preeditText != null)
                {
                    _preeditText = null;
                    _view.RequestInvalidate();
                }
            }

            /// <summary>
            /// Notifies the IME that the cursor rectangle has changed.
            /// Called when the terminal buffer updates and the cursor may have moved.
            /// </summary>
            internal void NotifyCursorRectangleChanged() => RaiseCursorRectangleChanged();

            /// <summary>
            /// Notifies the IME that the surrounding text has changed.
            /// </summary>
            internal void NotifySurroundingTextChanged() => RaiseSurroundingTextChanged();
        }


    }
}
