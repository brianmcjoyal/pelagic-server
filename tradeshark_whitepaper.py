#!/usr/bin/env python3
"""Generate TradeShark Whitepaper PDF"""

from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.colors import HexColor, white, black
from reportlab.lib.units import inch
from reportlab.lib.enums import TA_CENTER, TA_LEFT, TA_JUSTIFY
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,
    PageBreak, HRFlowable, KeepTogether
)
from reportlab.graphics.shapes import Drawing, Rect, String, Line
from reportlab.graphics import renderPDF

# Colors
DARK_BG = HexColor("#0a0a0a")
ACCENT_GREEN = HexColor("#00dc5a")
ACCENT_ORANGE = HexColor("#ff8c00")
ACCENT_BLUE = HexColor("#00d4ff")
ACCENT_PURPLE = HexColor("#e040fb")
DARK_CARD = HexColor("#141414")
GRAY_TEXT = HexColor("#444444")
MED_GRAY = HexColor("#888888")
LIGHT_GRAY = HexColor("#cccccc")
TABLE_HEADER_BG = HexColor("#1a1a2e")
TABLE_ROW_BG = HexColor("#111111")
TABLE_ALT_BG = HexColor("#0d0d0d")

def build_whitepaper():
    doc = SimpleDocTemplate(
        "/Users/brianmcjoyal/Desktop/TradeShark_Whitepaper.pdf",
        pagesize=letter,
        topMargin=0.75 * inch,
        bottomMargin=0.75 * inch,
        leftMargin=0.85 * inch,
        rightMargin=0.85 * inch,
    )

    styles = getSampleStyleSheet()

    # Custom styles
    styles.add(ParagraphStyle(
        "CoverTitle",
        parent=styles["Title"],
        fontSize=36,
        leading=42,
        textColor=white,
        alignment=TA_LEFT,
        spaceAfter=6,
        fontName="Helvetica-Bold",
    ))
    styles.add(ParagraphStyle(
        "CoverSubtitle",
        parent=styles["Normal"],
        fontSize=16,
        leading=22,
        textColor=ACCENT_GREEN,
        alignment=TA_LEFT,
        spaceAfter=4,
        fontName="Helvetica",
    ))
    styles.add(ParagraphStyle(
        "CoverBody",
        parent=styles["Normal"],
        fontSize=11,
        leading=16,
        textColor=MED_GRAY,
        alignment=TA_LEFT,
        fontName="Helvetica",
    ))
    styles.add(ParagraphStyle(
        "SectionHead",
        parent=styles["Heading1"],
        fontSize=22,
        leading=28,
        textColor=white,
        spaceBefore=24,
        spaceAfter=10,
        fontName="Helvetica-Bold",
    ))
    styles.add(ParagraphStyle(
        "SubHead",
        parent=styles["Heading2"],
        fontSize=15,
        leading=20,
        textColor=ACCENT_GREEN,
        spaceBefore=16,
        spaceAfter=6,
        fontName="Helvetica-Bold",
    ))
    styles.add(ParagraphStyle(
        "SubHead2",
        parent=styles["Heading3"],
        fontSize=12,
        leading=16,
        textColor=ACCENT_BLUE,
        spaceBefore=10,
        spaceAfter=4,
        fontName="Helvetica-Bold",
    ))
    styles.add(ParagraphStyle(
        "Body",
        parent=styles["Normal"],
        fontSize=10.5,
        leading=15,
        textColor=LIGHT_GRAY,
        alignment=TA_JUSTIFY,
        spaceAfter=8,
        fontName="Helvetica",
    ))
    styles.add(ParagraphStyle(
        "BulletCustom",
        parent=styles["Normal"],
        fontSize=10.5,
        leading=15,
        textColor=LIGHT_GRAY,
        leftIndent=18,
        spaceAfter=3,
        fontName="Helvetica",
    ))
    styles.add(ParagraphStyle(
        "Caption",
        parent=styles["Normal"],
        fontSize=9,
        leading=12,
        textColor=MED_GRAY,
        alignment=TA_CENTER,
        spaceBefore=4,
        spaceAfter=12,
        fontName="Helvetica-Oblique",
    ))
    styles.add(ParagraphStyle(
        "Footer",
        parent=styles["Normal"],
        fontSize=8,
        textColor=GRAY_TEXT,
        alignment=TA_CENTER,
    ))
    styles.add(ParagraphStyle(
        "Callout",
        parent=styles["Normal"],
        fontSize=10.5,
        leading=15,
        textColor=white,
        backColor=TABLE_HEADER_BG,
        borderPadding=(8, 10, 8, 10),
        spaceAfter=12,
        fontName="Helvetica",
    ))
    styles.add(ParagraphStyle(
        "CodeBlock",
        parent=styles["Normal"],
        fontSize=9,
        leading=13,
        textColor=ACCENT_GREEN,
        backColor=HexColor("#0d1117"),
        borderPadding=(8, 10, 8, 10),
        spaceAfter=10,
        fontName="Courier",
    ))

    story = []

    def hr():
        story.append(HRFlowable(
            width="100%", thickness=0.5,
            color=HexColor("#222222"), spaceBefore=6, spaceAfter=12
        ))

    def bullet(text):
        story.append(Paragraph(
            '<font color="#00dc5a">&bull;</font>&nbsp;&nbsp;' + text,
            styles["BulletCustom"]
        ))

    def metric_table(data, col_widths=None):
        """Create a styled data table."""
        if col_widths is None:
            col_widths = [1.6 * inch] * len(data[0])
        t = Table(data, colWidths=col_widths)
        style_cmds = [
            ("BACKGROUND", (0, 0), (-1, 0), TABLE_HEADER_BG),
            ("TEXTCOLOR", (0, 0), (-1, 0), ACCENT_GREEN),
            ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
            ("FONTSIZE", (0, 0), (-1, 0), 9),
            ("FONTSIZE", (0, 1), (-1, -1), 9),
            ("TEXTCOLOR", (0, 1), (-1, -1), LIGHT_GRAY),
            ("FONTNAME", (0, 1), (-1, -1), "Helvetica"),
            ("ALIGN", (0, 0), (-1, -1), "CENTER"),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
            ("GRID", (0, 0), (-1, -1), 0.5, HexColor("#1f1f1f")),
            ("TOPPADDING", (0, 0), (-1, -1), 6),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 6),
            ("LEFTPADDING", (0, 0), (-1, -1), 6),
            ("RIGHTPADDING", (0, 0), (-1, -1), 6),
        ]
        for i in range(1, len(data)):
            bg = TABLE_ROW_BG if i % 2 == 1 else TABLE_ALT_BG
            style_cmds.append(("BACKGROUND", (0, i), (-1, i), bg))
        t.setStyle(TableStyle(style_cmds))
        story.append(t)

    # ===========================
    # COVER PAGE
    # ===========================
    story.append(Spacer(1, 1.5 * inch))
    story.append(Paragraph("TradeShark", styles["CoverTitle"]))
    story.append(Paragraph(
        "Autonomous Prediction Market Trading System",
        styles["CoverSubtitle"]
    ))
    story.append(Spacer(1, 0.3 * inch))
    hr()
    story.append(Spacer(1, 0.15 * inch))
    story.append(Paragraph(
        "An algorithmic trading platform that identifies and exploits mispricings "
        "in live sports prediction markets using real-time sportsbook odds, "
        "game state analysis, and Kelly Criterion bet sizing.",
        styles["CoverBody"]
    ))
    story.append(Spacer(1, 0.6 * inch))

    cover_data = [
        ["Platform", "Kalshi (elections.kalshi.com)"],
        ["Markets", "Live Sports (NBA, NHL, MLB, NCAA, KBO, Tennis)"],
        ["Architecture", "Python/Flask on Railway with background threads"],
        ["Strategies", "Sniper, MoonShark, CloseGame"],
        ["Edge Source", "ESPN sportsbook odds + live game state"],
        ["Bet Sizing", "Half-Kelly Criterion with 5% bankroll cap"],
        ["Version", "v3.0-quant (launched March 2026)"],
    ]
    t = Table(cover_data, colWidths=[1.8 * inch, 4.2 * inch])
    t.setStyle(TableStyle([
        ("TEXTCOLOR", (0, 0), (0, -1), ACCENT_GREEN),
        ("TEXTCOLOR", (1, 0), (1, -1), LIGHT_GRAY),
        ("FONTNAME", (0, 0), (0, -1), "Helvetica-Bold"),
        ("FONTNAME", (1, 0), (1, -1), "Helvetica"),
        ("FONTSIZE", (0, 0), (-1, -1), 10),
        ("ALIGN", (0, 0), (0, -1), "RIGHT"),
        ("ALIGN", (1, 0), (1, -1), "LEFT"),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("TOPPADDING", (0, 0), (-1, -1), 5),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
        ("LEFTPADDING", (0, 0), (-1, -1), 8),
        ("RIGHTPADDING", (0, 0), (-1, -1), 8),
        ("LINEBELOW", (0, 0), (-1, -2), 0.5, HexColor("#1a1a1a")),
    ]))
    story.append(t)

    story.append(Spacer(1, 1.2 * inch))
    story.append(Paragraph(
        "Confidential  |  April 2026  |  Pelagic Systems",
        styles["Footer"]
    ))

    story.append(PageBreak())

    # ===========================
    # TABLE OF CONTENTS
    # ===========================
    story.append(Paragraph("Contents", styles["SectionHead"]))
    hr()
    toc_items = [
        ("1", "Executive Summary"),
        ("2", "The Opportunity"),
        ("3", "Platform Architecture"),
        ("4", "Trading Strategies"),
        ("5", "Edge Detection & Data Sources"),
        ("6", "Risk Management & Bet Sizing"),
        ("7", "Real-Time Execution Engine"),
        ("8", "Learning & Adaptation"),
        ("9", "Performance Tracking"),
        ("10", "Strategy Comparison"),
        ("11", "Security & Reliability"),
        ("12", "Roadmap"),
    ]
    for num, title in toc_items:
        story.append(Paragraph(
            f'<font color="#00dc5a">{num}.</font>&nbsp;&nbsp;&nbsp;{title}',
            styles["Body"]
        ))
    story.append(PageBreak())

    # ===========================
    # 1. EXECUTIVE SUMMARY
    # ===========================
    story.append(Paragraph("1. Executive Summary", styles["SectionHead"]))
    hr()
    story.append(Paragraph(
        "TradeShark is an autonomous prediction market trading system that identifies "
        "and exploits mispricings in live sports event contracts on Kalshi. The platform "
        "operates 24/7 with zero manual intervention, scanning live games every 15-30 seconds "
        "to find moments where Kalshi market prices diverge from real sportsbook odds.",
        styles["Body"]
    ))
    story.append(Paragraph(
        "The core thesis is simple: during live sporting events, prediction market prices "
        "lag behind reality. A basketball team that just went on a 12-0 run may have shifted "
        "from a 60% favorite to an 80% favorite on ESPN sportsbooks, but the Kalshi market "
        "still shows 65 cents. TradeShark detects this divergence and executes trades in "
        "the window before the market corrects.",
        styles["Body"]
    ))
    story.append(Paragraph(
        "The platform deploys three complementary strategies\u2014Sniper (high-probability favorites), "
        "MoonShark (mispriced underdogs), and CloseGame (late-game tight scores)\u2014each with "
        "independent risk budgets, conviction systems, and bet sizing governed by the Kelly Criterion.",
        styles["Body"]
    ))

    story.append(Paragraph("Key Design Principles", styles["SubHead"]))
    bullet("Zero guessing: every trade requires confirmed sportsbook odds data")
    bullet("Discipline over volume: reject 95%+ of scanned opportunities")
    bullet("Independent risk budgets per strategy prevent correlated blowups")
    bullet("Hold to settlement: no mid-game exits that crystallize noise as losses")
    bullet("Adaptive sizing: Kelly Criterion scales bets to edge strength and bankroll")

    story.append(PageBreak())

    # ===========================
    # 2. THE OPPORTUNITY
    # ===========================
    story.append(Paragraph("2. The Opportunity", styles["SectionHead"]))
    hr()
    story.append(Paragraph(
        "Prediction markets like Kalshi allow participants to buy binary contracts "
        "that settle at $1.00 if an event occurs and $0.00 if it does not. A contract "
        "priced at 75 cents implies the market assigns a 75% probability to the event. "
        "When this implied probability diverges from the true probability, an edge exists.",
        styles["Body"]
    ))

    story.append(Paragraph("Why Sports Markets Are Mispriced", styles["SubHead"]))
    bullet("<b>Latency</b> \u2014 Kalshi prices update slower than professional sportsbooks. "
           "ESPN moneylines shift within seconds of a scoring play; Kalshi may take minutes.")
    bullet("<b>Thin liquidity</b> \u2014 Many live sports markets have low volume, meaning a single "
           "large order can move prices away from fair value.")
    bullet("<b>Retail bias</b> \u2014 Kalshi's retail participant base tends to over-bet favorites "
           "and under-bet underdogs relative to true probabilities.")
    bullet("<b>Settlement mechanics</b> \u2014 Binary contracts have fixed expiry. Unlike sports betting, "
           "there's no vig recalculation\u2014the mispricing is locked in at entry.")

    story.append(Paragraph("The Edge Formula", styles["SubHead"]))
    story.append(Paragraph(
        "TradeShark's edge is the difference between the ESPN-implied probability "
        "(derived from live sportsbook moneylines) and the Kalshi market price:",
        styles["Body"]
    ))
    story.append(Paragraph(
        "Edge = ESPN Implied Probability - Kalshi Price / 100",
        styles["CodeBlock"]
    ))
    story.append(Paragraph(
        "A trade is only executed when this edge exceeds a minimum threshold (typically 3%), "
        "ensuring the expected value is positive after accounting for platform fees and variance.",
        styles["Body"]
    ))

    story.append(PageBreak())

    # ===========================
    # 3. PLATFORM ARCHITECTURE
    # ===========================
    story.append(Paragraph("3. Platform Architecture", styles["SectionHead"]))
    hr()

    story.append(Paragraph(
        "TradeShark runs as a single Python/Flask application deployed on Railway, "
        "with multiple background threads handling different responsibilities concurrently.",
        styles["Body"]
    ))

    story.append(Paragraph("System Components", styles["SubHead"]))

    arch_data = [
        ["Component", "Technology", "Role"],
        ["Web Server", "Flask + Gunicorn", "Dashboard UI, API endpoints, monitoring"],
        ["Main Scanner", "Daemon Thread", "Sniper + MoonShark scanning (15-30s interval)"],
        ["CloseGame Scanner", "Daemon Thread", "Dedicated 10-second fast loop for late games"],
        ["Kalshi API", "RSA-PSS Auth", "Order placement, position tracking, settlements"],
        ["ESPN API", "REST Polling", "Live scores, game state, sportsbook odds"],
        ["Data Store", "In-Memory + Disk", "Trade journal, learning state, category stats"],
        ["Deployment", "Railway (Cloud)", "Auto-deploy from GitHub, always-on"],
    ]
    metric_table(arch_data, col_widths=[1.5 * inch, 1.5 * inch, 3.0 * inch])

    story.append(Paragraph("Authentication", styles["SubHead"]))
    story.append(Paragraph(
        "All Kalshi API requests are authenticated using RSA-PSS digital signatures. "
        "Each request signs a payload of timestamp + HTTP method + path using a private key, "
        "with the signature and API key sent in custom headers. This ensures secure, "
        "tamper-proof communication without transmitting credentials.",
        styles["Body"]
    ))

    story.append(Paragraph("Scan Frequency", styles["SubHead"]))
    story.append(Paragraph(
        "The scanner adapts its frequency based on time of day to balance responsiveness "
        "with API rate limits:",
        styles["Body"]
    ))
    scan_data = [
        ["Time Window", "Scan Interval", "Rationale"],
        ["Peak Hours (4-10 PM PT)", "15 seconds", "Maximum live game activity"],
        ["Game Hours (10 AM-11 PM PT)", "30 seconds", "Active but less dense"],
        ["Off-Hours (11 PM-10 AM PT)", "5 minutes", "Minimal live action"],
        ["CloseGame (Always)", "10 seconds", "Dedicated thread, time-critical"],
    ]
    metric_table(scan_data, col_widths=[2.0 * inch, 1.5 * inch, 2.5 * inch])

    story.append(PageBreak())

    # ===========================
    # 4. TRADING STRATEGIES
    # ===========================
    story.append(Paragraph("4. Trading Strategies", styles["SectionHead"]))
    hr()
    story.append(Paragraph(
        "TradeShark deploys three independent strategies, each targeting a different "
        "market inefficiency with its own risk budget and conviction system.",
        styles["Body"]
    ))

    # SNIPER
    story.append(Paragraph("4.1 Live Game Sniper", styles["SubHead"]))
    story.append(Paragraph(
        "The Sniper strategy targets high-probability favorites in live sports markets. "
        "It looks for contracts priced between 65-85 cents where the game is actively "
        "in progress and the outcome is trending toward confirmation.",
        styles["Body"]
    ))
    story.append(Paragraph("Entry Criteria", styles["SubHead2"]))
    bullet("Market price between <b>65-85 cents</b> (sweet spot for win rate vs. payout)")
    bullet("Game must be <b>actively in progress</b> (confirmed via ESPN live scores)")
    bullet("Contract volume <b>&gt; 100</b> (sufficient liquidity)")
    bullet("Category not in blocklist (no weather, golf, politics, economics)")
    bullet("No existing position on the same event (global event lock)")
    bullet("Conviction score <b>&ge; 2</b> from signal aggregation")

    story.append(Paragraph("Conviction Signals", styles["SubHead2"]))
    conv_sniper = [
        ["Signal", "Points", "Condition"],
        ["Live Game", "+2", "ESPN confirms game in progress"],
        ["Close Game", "+1", "Score margin within 5 points"],
        ["Post-Game Settling", "+1", "Game ended, market settling"],
        ["High Volume", "+1", "Ask size >= 50 contracts"],
        ["Sweet Spot Price", "+1", "Entry at 75-88 cents"],
        ["Closing Boost", "+1", "Market closes within 30 minutes"],
    ]
    metric_table(conv_sniper, col_widths=[1.8 * inch, 0.8 * inch, 3.4 * inch])

    story.append(Spacer(1, 0.15 * inch))
    story.append(Paragraph(
        "<b>Daily Budget:</b> $150 &nbsp;|&nbsp; <b>Max Trades:</b> 20 &nbsp;|&nbsp; "
        "<b>Max Per Trade:</b> $25",
        styles["Callout"]
    ))

    # MOONSHARK
    story.append(Paragraph("4.2 MoonShark", styles["SubHead"]))
    story.append(Paragraph(
        "MoonShark hunts mispriced underdogs\u2014cheap contracts (25-40 cents) where "
        "ESPN sportsbook odds suggest the true probability is meaningfully higher than "
        "the Kalshi price implies. Small bets with outsized payouts.",
        styles["Body"]
    ))
    story.append(Paragraph("Entry Criteria", styles["SubHead2"]))
    bullet("Market price between <b>25-40 cents</b>")
    bullet("ESPN sportsbook edge <b>&ge; 3%</b> (hard requirement, no exceptions)")
    bullet("Game must be <b>live and in progress</b>")
    bullet("<b>Zero guessing:</b> if no ESPN odds data exists, the trade is skipped entirely")

    story.append(Paragraph("Edge Calculation", styles["SubHead2"]))
    story.append(Paragraph(
        "espn_edge = espn_implied_probability - (kalshi_price / 100)<br/>"
        "if espn_edge &lt; 0.03: skip  # Minimum 3% edge required<br/>"
        "if espn_data is None: skip   # No data = no trade",
        styles["CodeBlock"]
    ))
    story.append(Paragraph(
        "Example: ESPN moneyline implies a team has a 32% win probability. Kalshi prices "
        "the contract at 24 cents (24% implied). The edge is +8%\u2014well above the 3% "
        "threshold\u2014triggering a buy.",
        styles["Body"]
    ))
    story.append(Paragraph(
        "<b>Daily Budget:</b> $75 &nbsp;|&nbsp; <b>Max Trades:</b> 10 &nbsp;|&nbsp; "
        "<b>Max Per Trade:</b> $25",
        styles["Callout"]
    ))

    # CLOSEGAME
    story.append(Paragraph("4.3 CloseGame", styles["SubHead"]))
    story.append(Paragraph(
        "CloseGame exploits the sharpest mispricings: late-stage games with tight scores. "
        "When a basketball game is tied with 3 minutes left, the contract at 45 cents often "
        "understates the true 50/50 probability. This strategy runs on a dedicated 10-second "
        "scan loop to capture these fleeting opportunities.",
        styles["Body"]
    ))
    story.append(Paragraph("Sport-Specific Thresholds", styles["SubHead2"]))
    cg_data = [
        ["Sport", "Required Period", "Max Score Margin"],
        ["NBA", "4th Quarter", "6 points"],
        ["NCAA Basketball", "2nd Half", "5 points"],
        ["NHL", "3rd Period", "1 goal"],
        ["MLB", "7th Inning+", "3 runs"],
        ["Tennis", "Any Set", "Always eligible"],
    ]
    metric_table(cg_data, col_widths=[1.8 * inch, 2.0 * inch, 2.2 * inch])

    story.append(Spacer(1, 0.1 * inch))
    story.append(Paragraph(
        "<b>Daily Budget:</b> $25 &nbsp;|&nbsp; <b>Max Trades:</b> 5 &nbsp;|&nbsp; "
        "<b>Scan Loop:</b> 10 seconds &nbsp;|&nbsp; <b>ESPN Edge:</b> &ge; 3%",
        styles["Callout"]
    ))

    story.append(PageBreak())

    # ===========================
    # 5. EDGE DETECTION & DATA SOURCES
    # ===========================
    story.append(Paragraph("5. Edge Detection & Data Sources", styles["SectionHead"]))
    hr()

    story.append(Paragraph(
        "TradeShark's primary competitive advantage is its integration of multiple real-time "
        "data sources to quantify edge before any trade is placed. No trade is executed "
        "based on price alone.",
        styles["Body"]
    ))

    story.append(Paragraph("5.1 ESPN Live Scores & Sportsbook Odds", styles["SubHead"]))
    story.append(Paragraph(
        "The ESPN API provides both live game state data and embedded sportsbook moneylines. "
        "TradeShark polls these endpoints every 15-30 seconds across all major leagues:",
        styles["Body"]
    ))
    espn_data = [
        ["League", "ESPN Endpoint", "Data Extracted"],
        ["NBA", "basketball/nba/scoreboard", "Score, quarter, clock, moneylines"],
        ["NHL", "hockey/nhl/scoreboard", "Score, period, clock, moneylines"],
        ["MLB", "baseball/mlb/scoreboard", "Score, inning, count, moneylines"],
        ["NCAA M", "basketball/mens-college-basketball", "Score, half, clock, moneylines"],
        ["NCAA W", "basketball/womens-college-basketball", "Score, half, clock, moneylines"],
        ["KBO", "baseball/kbo/scoreboard", "Score, inning, moneylines"],
    ]
    metric_table(espn_data, col_widths=[0.8 * inch, 2.8 * inch, 2.4 * inch])

    story.append(Paragraph("5.2 Kalshi Order Book", styles["SubHead"]))
    story.append(Paragraph(
        "Real-time order book data is fetched for every candidate trade to assess liquidity "
        "and optimize entry price. The system analyzes bid/ask spread, depth at each level, "
        "order book imbalance, and total liquidity. Orders are placed aggressively at +3 cents "
        "above the best ask to ensure fills in fast-moving markets.",
        styles["Body"]
    ))

    story.append(Paragraph("5.3 Cross-Platform Validation", styles["SubHead"]))
    story.append(Paragraph(
        "TradeShark cross-references prices across five prediction market platforms to validate "
        "consensus pricing and identify arbitrage opportunities:",
        styles["Body"]
    ))
    bullet("<b>Polymarket</b> \u2014 Largest crypto prediction market (2% fee)")
    bullet("<b>PredictIt</b> \u2014 Political prediction market (10% fee)")
    bullet("<b>Manifold</b> \u2014 Play-money market with real signal (0% fee)")
    bullet("<b>Metaculus</b> \u2014 Calibrated forecasting platform")
    bullet("<b>Smarkets</b> \u2014 UK betting exchange")

    story.append(Paragraph("5.4 Game State Analysis", styles["SubHead"]))
    story.append(Paragraph(
        "Beyond raw odds, TradeShark tracks granular game state to contextualize each trade. "
        "This includes current scores and margin, game period and time remaining, "
        "momentum direction and velocity (price movement over 3-minute windows), "
        "and whether the team being bet on is currently leading or trailing. "
        "This context is recorded with every trade for post-hoc analysis.",
        styles["Body"]
    ))

    story.append(PageBreak())

    # ===========================
    # 6. RISK MANAGEMENT
    # ===========================
    story.append(Paragraph("6. Risk Management & Bet Sizing", styles["SectionHead"]))
    hr()

    story.append(Paragraph("6.1 Kelly Criterion", styles["SubHead"]))
    story.append(Paragraph(
        "All bet sizing is governed by the Kelly Criterion, the mathematically optimal "
        "formula for maximizing long-term bankroll growth given known edge and odds. "
        "TradeShark uses Half-Kelly (50% of the optimal fraction) to reduce variance "
        "while retaining approximately 75% of the theoretical growth rate.",
        styles["Body"]
    ))
    story.append(Paragraph(
        "kelly_fraction = (b * p - q) / b<br/>"
        "  where b = decimal odds, p = win probability, q = 1 - p<br/>"
        "half_kelly = kelly_fraction / 2<br/>"
        "capped = min(half_kelly, 0.05)  # 5% bankroll cap<br/>"
        "bet = bankroll * capped<br/>"
        "final_bet = min(bet, $25)  # Hard ceiling",
        styles["CodeBlock"]
    ))
    story.append(Paragraph(
        "This means bet size scales naturally with bankroll: a $500 bankroll produces smaller "
        "bets than a $2,000 bankroll on the same edge, preventing ruin during drawdowns.",
        styles["Body"]
    ))

    story.append(Paragraph("6.2 Layered Risk Controls", styles["SubHead"]))
    risk_data = [
        ["Control", "Value", "Purpose"],
        ["Max Bet Per Trade", "$25", "Prevent single-trade blowup"],
        ["Half-Kelly Sizing", "50% of optimal", "Reduce variance, prevent overbetting"],
        ["5% Bankroll Cap", "Per trade", "No trade risks more than 5% of capital"],
        ["Daily Budget (Sniper)", "$150 / 20 trades", "Strategy-level risk isolation"],
        ["Daily Budget (MoonShark)", "$75 / 10 trades", "Smaller budget for higher-risk bets"],
        ["Daily Budget (CloseGame)", "$25 / 5 trades", "Smallest budget (least proven)"],
        ["Balance Floor", "$250 minimum", "Auto-disable bot if breached"],
        ["Category Cap", "3 positions max", "Diversification across sports"],
        ["Event Lock", "1 position per event", "No doubling down on same game"],
    ]
    metric_table(risk_data, col_widths=[1.8 * inch, 1.3 * inch, 2.9 * inch])

    story.append(Paragraph("6.3 Category-Based Blocking", styles["SubHead"]))
    story.append(Paragraph(
        "TradeShark maintains a blocklist of categories with historically zero or near-zero "
        "win rates. These categories are hard-blocked from all strategies regardless of "
        "apparent edge: weather events, golf, politics, economics, NFL offseason, "
        "and specific keywords like \"gas price\" and \"netflix.\" "
        "The learning engine can dynamically add categories to this list when a sport "
        "accumulates 3+ trades with a 0% win rate.",
        styles["Body"]
    ))

    story.append(Paragraph("6.4 Hold-to-Settlement Policy", styles["SubHead"]))
    story.append(Paragraph(
        "TradeShark holds all positions to settlement rather than trading mid-event. "
        "Binary contracts settle at $0 or $1\u2014price swings during a live game are "
        "noise, not signal. Early exits crystallize temporary drawdowns as permanent losses "
        "and forfeit the edge that justified the entry. The only exception is a confirmed "
        "blowout exit when a game becomes non-competitive (e.g., 30-point NBA lead).",
        styles["Body"]
    ))

    story.append(PageBreak())

    # ===========================
    # 7. REAL-TIME EXECUTION
    # ===========================
    story.append(Paragraph("7. Real-Time Execution Engine", styles["SectionHead"]))
    hr()

    story.append(Paragraph("7.1 Scan Cycle", styles["SubHead"]))
    story.append(Paragraph(
        "Each main scan cycle executes the following pipeline in sequence:",
        styles["Body"]
    ))
    bullet("<b>Cycle 1:</b> Run Sniper scan + MoonShark scan across all live markets")
    bullet("<b>Cycle 1-2:</b> Check for newly settled positions, reinvest freed capital")
    bullet("<b>Cycle 1+:</b> Sync external Kalshi fills (detect manual trades)")
    bullet("<b>Cycle 3:</b> Monitor live game scores and update game state cache")
    bullet("<b>Cycle 10:</b> Regenerate high-confidence market picks, warm caches")
    bullet("<b>Cycle 120:</b> Run the learning engine (recompute category multipliers)")

    story.append(Paragraph("7.2 Order Execution", styles["SubHead"]))
    story.append(Paragraph(
        "Orders are placed as limit orders with aggressive pricing to ensure fills in "
        "fast-moving markets. Buy orders are submitted at +3 cents above the current best "
        "ask. If an order fails, the system retries with an immediate-or-cancel order type. "
        "A global event lock prevents placing duplicate orders on the same game, and all "
        "order IDs are tracked to prevent re-processing.",
        styles["Body"]
    ))

    story.append(Paragraph("7.3 Settlement & Reinvestment", styles["SubHead"]))
    story.append(Paragraph(
        "When a position settles, TradeShark detects it via the Kalshi portfolio API, "
        "records the realized P&L in the trade journal, updates category statistics, "
        "and immediately redeploys the freed capital into the next available opportunity. "
        "This cycle ensures capital is never idle when edge exists.",
        styles["Body"]
    ))

    story.append(PageBreak())

    # ===========================
    # 8. LEARNING & ADAPTATION
    # ===========================
    story.append(Paragraph("8. Learning & Adaptation", styles["SectionHead"]))
    hr()

    story.append(Paragraph(
        "TradeShark incorporates a learning engine that adjusts future behavior based on "
        "historical performance. The system runs a full analysis pass every ~30 minutes "
        "once sufficient trade data exists (minimum 10 settled trades).",
        styles["Body"]
    ))

    story.append(Paragraph("8.1 Category Multipliers", styles["SubHead"]))
    story.append(Paragraph(
        "Win rates are tracked per sport/category. These rates feed back into bet sizing "
        "as dynamic multipliers:",
        styles["Body"]
    ))
    mult_data = [
        ["Category Win Rate", "Bet Multiplier", "Action"],
        [">= 25%", "1.5x", "Proven winner \u2014 increase allocation"],
        ["15-25%", "1.25x", "Solid performer \u2014 slight increase"],
        ["10-15%", "1.0x", "Neutral \u2014 standard sizing"],
        ["1-10%", "0.5x", "Weak \u2014 reduce allocation"],
        ["0% (3+ trades)", "0.0x", "Hard block \u2014 stop trading this category"],
    ]
    metric_table(mult_data, col_widths=[1.6 * inch, 1.3 * inch, 3.1 * inch])

    story.append(Paragraph("8.2 Multi-Dimensional Analysis", styles["SubHead"]))
    story.append(Paragraph(
        "The learning engine analyzes performance across multiple dimensions to identify "
        "patterns and refine strategy parameters:",
        styles["Body"]
    ))
    bullet("<b>Price bucket analysis:</b> Win rate segmented by entry price (e.g., 60-75 cents vs. 75-90 cents)")
    bullet("<b>Game state analysis:</b> Win rate by score margin, period, and time-to-close")
    bullet("<b>Edge confidence:</b> Win rate bucketed by ESPN edge magnitude")
    bullet("<b>Entry timing:</b> Time-of-day effects on win rate")
    bullet("<b>Strategy comparison:</b> Relative performance of Sniper vs. MoonShark vs. CloseGame")
    bullet("<b>Momentum analysis:</b> Tracks price movement velocity over 3-minute rolling windows")

    story.append(PageBreak())

    # ===========================
    # 9. PERFORMANCE TRACKING
    # ===========================
    story.append(Paragraph("9. Performance Tracking", styles["SectionHead"]))
    hr()

    story.append(Paragraph(
        "Every trade is recorded in a comprehensive journal with full context about "
        "why the bet was placed, what data supported it, and how it resolved. "
        "The Performance dashboard displays real-time KPIs and a running trade feed.",
        styles["Body"]
    ))

    story.append(Paragraph("9.1 Key Performance Indicators", styles["SubHead"]))
    kpi_data = [
        ["Metric", "Formula", "Purpose"],
        ["Win Rate", "Wins / Total Trades", "Raw hit rate"],
        ["ROI", "Total P&L / Total Wagered", "Return efficiency"],
        ["Profit Factor", "(Avg Win x Wins) / (Avg Loss x Losses)", "Quality of wins vs. losses"],
        ["Expectancy", "Total P&L / Total Trades", "Expected value per trade"],
        ["Payoff Ratio", "Avg Win / Avg Loss", "Win size vs. loss size"],
        ["Max Drawdown", "Peak to trough cumulative P&L", "Worst losing streak"],
        ["Sharpe Ratio", "Mean Daily P&L / Std Dev", "Risk-adjusted returns"],
    ]
    metric_table(kpi_data, col_widths=[1.3 * inch, 2.5 * inch, 2.2 * inch])

    story.append(Paragraph("9.2 Trade Journal", styles["SubHead"]))
    story.append(Paragraph(
        "Each trade record captures the full decision context: entry price and contract count, "
        "ESPN edge percentage at time of entry, conviction score and contributing signals, "
        "game state (score, period, clock), the strategy that triggered the trade, "
        "edge reasons (human-readable explanation of why the bet qualified), "
        "and outcome with realized P&L. This data persists across server restarts via "
        "Kalshi API reconstruction and enables rigorous post-hoc analysis of every decision.",
        styles["Body"]
    ))

    story.append(PageBreak())

    # ===========================
    # 10. STRATEGY COMPARISON
    # ===========================
    story.append(Paragraph("10. Strategy Comparison", styles["SectionHead"]))
    hr()

    comp_data = [
        ["", "Sniper", "MoonShark", "CloseGame"],
        ["Thesis", "High-prob favorites", "Mispriced underdogs", "Late tight games"],
        ["Price Range", "65-85 cents", "25-40 cents", "30-45 cents"],
        ["Edge Source", "ESPN + timing", "ESPN edge >= 3%", "ESPN edge >= 3%"],
        ["Daily Budget", "$150", "$75", "$25"],
        ["Max Trades/Day", "20", "10", "5"],
        ["Scan Interval", "30 seconds", "30 seconds", "10 seconds"],
        ["Risk Profile", "Conservative", "Aggressive", "Moderate"],
        ["Payout Profile", "Small, frequent", "Large, infrequent", "Medium"],
        ["Thread", "Main loop", "Main loop", "Dedicated"],
    ]
    metric_table(comp_data, col_widths=[1.4 * inch, 1.5 * inch, 1.5 * inch, 1.6 * inch])

    story.append(Spacer(1, 0.2 * inch))
    story.append(Paragraph(
        "The three strategies are designed to be complementary. Sniper provides steady "
        "base returns from high-probability outcomes. MoonShark adds convexity\u2014most bets "
        "lose, but winners pay 2-4x. CloseGame captures the sharpest edges in the most "
        "volatile moments. Each strategy has an independent daily budget, preventing a "
        "bad day in one strategy from consuming capital earmarked for another.",
        styles["Body"]
    ))

    story.append(PageBreak())

    # ===========================
    # 11. SECURITY & RELIABILITY
    # ===========================
    story.append(Paragraph("11. Security & Reliability", styles["SectionHead"]))
    hr()

    story.append(Paragraph("11.1 Authentication Security", styles["SubHead"]))
    story.append(Paragraph(
        "Kalshi API authentication uses RSA-PSS digital signatures with SHA-256 hashing. "
        "Private keys are stored as environment variables on Railway, never in source code. "
        "Each request generates a unique signature from the current timestamp, preventing "
        "replay attacks.",
        styles["Body"]
    ))

    story.append(Paragraph("11.2 State Persistence", styles["SubHead"]))
    bullet("<b>Primary:</b> In-memory state with periodic disk flush to /tmp/pelagic_state.json")
    bullet("<b>Fallback:</b> Full state reconstruction from Kalshi API on startup")
    bullet("<b>Trade Journal:</b> Rebuilt from Kalshi settled positions (survives Railway deploys)")
    bullet("<b>Learning State:</b> Version-controlled, rebuilds from trade journal if lost")

    story.append(Paragraph("11.3 Uptime & Monitoring", styles["SubHead"]))
    bullet("Keep-alive watchdog pings own /health endpoint every 5 minutes")
    bullet("Auto-restart of dead background threads via _ensure_bg_thread() hook")
    bullet("Discord webhook notifications for all trade activity, settlements, and errors")
    bullet("Real-time dashboard with live feed, position monitor, and closing-soon tracker")

    story.append(PageBreak())

    # ===========================
    # 12. ROADMAP
    # ===========================
    story.append(Paragraph("12. Roadmap", styles["SectionHead"]))
    hr()

    story.append(Paragraph("Near-Term Improvements", styles["SubHead"]))
    bullet("Expand ESPN edge tracking to additional sports (soccer, tennis, MMA)")
    bullet("Improve win rate through tighter conviction thresholds based on learning data")
    bullet("Add live order book momentum as an entry signal")
    bullet("Implement cross-platform arbitrage for simultaneous buys across Kalshi + Polymarket")

    story.append(Paragraph("Medium-Term Goals", styles["SubHead"]))
    bullet("Machine learning model trained on historical trade outcomes to predict settlement")
    bullet("Dynamic strategy weighting based on rolling performance")
    bullet("Expand to non-sports markets (economic indicators, elections) once edge is proven")
    bullet("Portfolio-level Kelly sizing across correlated positions")

    story.append(Paragraph("Long-Term Vision", styles["SubHead"]))
    story.append(Paragraph(
        "TradeShark aims to become a fully autonomous, self-improving prediction market "
        "trading system. As the learning engine accumulates more data, the system will "
        "progressively narrow its focus to the highest-edge opportunities and automatically "
        "allocate capital across strategies based on rolling risk-adjusted returns. "
        "The endgame is a system that requires zero human oversight while consistently "
        "extracting value from prediction market inefficiencies.",
        styles["Body"]
    ))

    story.append(Spacer(1, 1.0 * inch))
    hr()
    story.append(Paragraph(
        "Confidential  |  Pelagic Systems  |  April 2026",
        styles["Footer"]
    ))

    # Build with dark background
    def on_page(canvas_obj, doc_obj):
        canvas_obj.saveState()
        canvas_obj.setFillColor(DARK_BG)
        canvas_obj.rect(0, 0, letter[0], letter[1], fill=True, stroke=False)
        # Page number
        canvas_obj.setFillColor(GRAY_TEXT)
        canvas_obj.setFont("Helvetica", 8)
        canvas_obj.drawCentredString(letter[0] / 2, 0.4 * inch, f"{doc_obj.page}")
        canvas_obj.restoreState()

    doc.build(story, onFirstPage=on_page, onLaterPages=on_page)
    print("Whitepaper generated: /Users/brianmcjoyal/Desktop/TradeShark_Whitepaper.pdf")

if __name__ == "__main__":
    build_whitepaper()
