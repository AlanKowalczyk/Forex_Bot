"""
Forex Trading Bot Version 7 - Built on Version 6
Key Changes:
- REMOVED ALL SL LOGIC to prevent partial grid closures
- Only TP management and next grid positioning
- Eliminated spam logging - only logs when actions are taken
- Simplified grid management without SL complexity
"""
import pandas as pd
import datetime as dt
from apscheduler.schedulers.background import BackgroundScheduler
from time import sleep
import pandas_ta as ta
from oandapyV20 import API
import oandapyV20.endpoints.orders as orders
import oandapyV20.endpoints.trades as trades
import oandapyV20.endpoints.pricing as pricing
import oandapyV20.endpoints.accounts as accounts
import oandapyV20.endpoints.transactions as transactions
from oandapyV20.contrib.requests import MarketOrderRequest
from oanda_candles import Pair, Gran, CandleClient
from config import access_token, account_ID # eurusd
from oanda_bot_config import *
import logging
import time
import os
import sys
import signal
import random
from functools import wraps

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Suppress INFO logs from external libraries
logging.getLogger("apscheduler").setLevel(logging.ERROR)
logging.getLogger("oandapyV20").setLevel(logging.WARNING)

# === DEBUG SIGNAL LOGGER ===
debug_logger = logging.getLogger('debug_signals')
debug_logger.setLevel(logging.INFO)
debug_logger.propagate = False  # Prevent propagation to root logger (console output)
debug_handler = logging.FileHandler('debug_signals.log')
debug_handler.setFormatter(logging.Formatter('%(asctime)s - %(message)s'))
debug_logger.addHandler(debug_handler)

# === DEBUGGING FUNCTIONALITY ===
# These variables are used to track and report bot status every 6 hours for debugging purposes
DEBUG_STATUS_INTERVAL_HOURS = 6  # Print status every 6 hours
DEBUG_LAST_STATUS_TIME = None    # Track when last status was printed

def retry_on_error(max_retries=3, base_delay=1.0, max_delay=30.0, backoff_factor=2.0):
    """
    Decorator for retrying API calls with exponential backoff.
    
    Args:
        max_retries: Maximum number of retry attempts
        base_delay: Initial delay between retries (seconds)
        max_delay: Maximum delay between retries (seconds)
        backoff_factor: Multiplier for exponential backoff
    """
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            last_exception = None
            
            for attempt in range(max_retries + 1):
                try:
                    return func(*args, **kwargs)
                except Exception as e:
                    last_exception = e
                    error_str = str(e).lower()
                    
                    # Check if it's a recoverable error
                    recoverable_errors = [
                        'connection', 'timeout', 'network', 'dns', 'resolve',
                        'unreachable', 'temporary', 'service unavailable',
                        'rate limit', 'too many requests', 'server error'
                    ]
                    
                    is_recoverable = any(error in error_str for error in recoverable_errors)
                    
                    if attempt == max_retries or not is_recoverable:
                        # Final attempt or non-recoverable error
                        if hasattr(args[0], '__class__'):
                            class_name = args[0].__class__.__name__
                            logging.error(f"{class_name}.{func.__name__}() failed after {attempt + 1} attempts: {e}")
                        else:
                            logging.error(f"{func.__name__}() failed after {attempt + 1} attempts: {e}")
                        break
                    
                    # Calculate delay with jitter
                    delay = min(base_delay * (backoff_factor ** attempt), max_delay)
                    jitter = random.uniform(0.5, 1.5)
                    actual_delay = delay * jitter
                    
                    logging.warning(f"{func.__name__}() attempt {attempt + 1} failed: {e}. Retrying in {actual_delay:.1f}s...")
                    time.sleep(actual_delay)
            
            # If we get here, all retries failed
            raise last_exception
        
        return wrapper
    return decorator

class TradingBot:
    def __init__(self):
        self.instrument = PAIR
        self.tp_pips = TP_PIPS
        self.grid_distance_pips = GRID_DISTANCE_PIPS
        self.grid_tp_pips = GRID_TP_PIPS
        self.open_positions = {'buy': [], 'sell': []}
        self.api = API(access_token)
        self.account_ID = account_ID
        self.pip_location = PIP_LOCATION
        self.instrument_precision = INSTRUMENT_PRECISION
        self.martingale_sequence = MARTINGALE_SEQUENCE
        self.last_collective_tp = {'buy': None, 'sell': None}
        self.instrument_prefix = self.instrument.lower().replace('_', '')
        self.last_open_trade_ids_file = f'/tmp/oanda_{self.instrument_prefix}_last_open_trade_ids.txt'
        self.swap_flag_file = f'/tmp/oanda_{self.instrument_prefix}_swap_adjusted.flag'
        self.prev_open_trade_ids = self._load_last_open_trade_ids()
        self.quote_currency = self.instrument.split('_')[1]  # e.g., 'CAD' from 'NZD_CAD'
        
        # Profit-based TP calculation parameters
        self.profit_target_per_lot = PROFIT_TARGET_PER_LOT
        self.fallback_pip_values = FALLBACK_PIP_VALUES
        self.quote_currency_rate = QUOTE_CURRENCY_RATE
        self.account_currency = 'GBP'  # Your account currency
        self.quote_to_account_rate = QUOTE_CURRENCY_RATE  # Initialize with config fallback
        
        # Try to fetch exchange rate once at startup
        self.fetch_startup_exchange_rate()
        
        # === FINANCING/SWAP TRACKING ===
        # Track last financing check time to minimize API calls
        self.last_financing_check = dt.datetime.now(dt.timezone.utc) - dt.timedelta(hours=1)
        # Store actual daily financing amounts for TP recalculation
        self.daily_financing_history = {}  # {date: {direction: amount}}
        self.financing_log_file = f'financing_data_{self.instrument_prefix}.json'
        self.financing_adjustment = {'buy': 0, 'sell': 0}  # Real-time financing adjustment for TP calculation per direction
        
        # Load historical financing data
        self.load_financing_data()
        
        logging.info(f"[STARTUP] TradingBot v7 (NO-SL) initialized for instrument: {self.instrument}")
        logging.info(f"[STARTUP] Quote to account rate: {self.quote_to_account_rate:.4f}")
        logging.info(f"[STARTUP] SL DISABLED - Only TP and grid management active")
        self.last_tp_per_trade = {}  # Track last TP set per trade ID
        self.last_grid_state = {'buy': None, 'sell': None}  # Track last grid state for each direction
        self.initialized = False  # Track if initial setup is done

    def get_vwap(self, direction):
        """Calculate Volume Weighted Average Price for a grid"""
        grid = self.open_positions[direction]
        if not grid:
            return None
        total_units = sum(trade['units'] for trade in grid)
        vwap_numerator = sum(trade['price'] * trade['units'] for trade in grid)
        if total_units == 0:
            return None
        return vwap_numerator / total_units

    def fetch_startup_exchange_rate(self):
        """Fetches exchange rate once at startup with proper fallback"""
        if self.quote_currency == self.account_currency:
            self.quote_to_account_rate = 1.0
            logging.info(f"[STARTUP] Same currency, rate set to 1.0")
            return True

        # Determine the correct OANDA pair format based on forex conventions
        # Major currencies typically appear as base currency: GBP_USD, EUR_USD, etc.
        major_currencies = ['EUR', 'GBP', 'AUD', 'NZD']
        
        if self.account_currency in major_currencies and self.quote_currency not in major_currencies:
            # Account currency is major, use it as base: GBP_USD
            rate_pair = f"{self.account_currency}_{self.quote_currency}"
            invert_rate = True
        elif self.quote_currency in major_currencies and self.account_currency not in major_currencies:
            # Quote currency is major, use it as base: GBP_JPY (if account was JPY)
            rate_pair = f"{self.quote_currency}_{self.account_currency}"
            invert_rate = False
        elif self.account_currency == 'GBP' and self.quote_currency == 'USD':
            # Special case: GBP_USD is the standard pair
            rate_pair = "GBP_USD"
            invert_rate = True
        elif self.account_currency == 'USD' and self.quote_currency in major_currencies:
            # USD as account, major quote: EUR_USD, GBP_USD
            rate_pair = f"{self.quote_currency}_USD"
            invert_rate = False
        else:
            # Default: try quote_account format first
            rate_pair = f"{self.quote_currency}_{self.account_currency}"
            invert_rate = False
        
        try:
            r = pricing.PricingInfo(accountID=self.account_ID, params={'instruments': rate_pair})
            response = self.api.request(r)
            rate = float(response['prices'][0]['bids'][0]['price'])
            
            # Invert rate if needed to get quote_to_account rate
            if invert_rate:
                rate = 1.0 / rate
            
            self.quote_to_account_rate = rate
            logging.info(f"[STARTUP] Fetched {rate_pair} rate, quote to account rate: {self.quote_to_account_rate:.5f}")
            return True
        except Exception as e:
            logging.warning(f"[STARTUP] Could not fetch {rate_pair} rate: {e}, using config fallback: {self.quote_currency_rate}")
            self.quote_to_account_rate = self.quote_currency_rate
            return False

    def calculate_profit_based_tp(self, direction, grid):
        """
        Calculates a collective TP price based on a fixed monetary profit target
        scaled by the total lot size. Uses startup exchange rate.

        Args:
            direction (str): 'buy' or 'sell'.
            grid (list): The list of open trades in the grid.

        Returns:
            float: The calculated Take Profit price, or None if calculation fails.
        """
        if not grid:
            return None

        # --- 1. Define Your Profit Target ---
        profit_factor = self.profit_target_per_lot  # £150 profit per full lot
        total_size = sum(trade['units'] for trade in grid) / 100_000  # Total size in lots
        target_profit_gbp = total_size * profit_factor
        
        # Apply financing adjustment to profit target
        if hasattr(self, 'financing_adjustment') and self.financing_adjustment.get(direction) is not None:
            financing_adj_factor = 1.0 + self.financing_adjustment[direction]
            target_profit_gbp *= financing_adj_factor
            logging.info(f"Applied financing adjustment to profit target: £{total_size * profit_factor:.2f} → £{target_profit_gbp:.2f}")

        # --- 2. Calculate Profit-per-Pip for the Grid ---
        pip_value_location = self.get_pip_value_for_instrument()
        total_units = sum(trade['units'] for trade in grid)
        
        # Convert pip value from quote currency to account currency (GBP)
        grid_profit_per_pip_gbp = (total_units * pip_value_location) * self.quote_to_account_rate

        if grid_profit_per_pip_gbp <= 0:
            logging.warning(f"Invalid pip value calculation: {grid_profit_per_pip_gbp}")
            return None

        # --- 3. Calculate Required Pips and Final TP Price ---
        required_pips = target_profit_gbp / grid_profit_per_pip_gbp
        
        # Get the grid's break-even price
        vwap = self.get_vwap(direction)
        if vwap is None:
            return None
        
        if direction == 'buy':
            tp_price = vwap + (required_pips * pip_value_location)
        else:  # 'sell'
            tp_price = vwap - (required_pips * pip_value_location)
            
        logging.info(f"Calculated TP for {direction} grid: Target Profit=£{target_profit_gbp:.2f}, "
                  f"Required Pips={required_pips:.1f}, VWAP={vwap:.5f}, TP Price={tp_price:.5f}")
        
        return tp_price

    def _load_last_open_trade_ids(self):
        try:
            if os.path.exists(self.last_open_trade_ids_file):
                with open(self.last_open_trade_ids_file, 'r') as f:
                    ids = f.read().strip().split(',')
                    return set([x for x in ids if x])
        except Exception:
            pass
        return set()

    def _save_last_open_trade_ids(self, trade_ids):
        try:
            with open(self.last_open_trade_ids_file, 'w') as f:
                f.write(','.join(trade_ids))
        except Exception:
            pass

    @retry_on_error(max_retries=3, base_delay=1.0, max_delay=15.0)
    def get_candles(self, n, timeframe=None):
        if timeframe is None:
            timeframe = CANDLE_TIMEFRAME
        # Convert string timeframe to Gran enum if needed
        tf = getattr(Gran, timeframe) if isinstance(timeframe, str) else timeframe
        try:
            client = CandleClient(access_token, real=False)
            # Keep the underscore for Pair enum lookup (e.g., "EUR_USD" -> Pair.EUR_USD)
            pair = getattr(Pair, self.instrument)  # OANDA pairs match Pair enum names exactly
            collector = client.get_collector(pair, tf)
            candles = collector.grab(n)
            return candles
        except Exception as e:
            logging.error(f"Error fetching candles: {e}")
            return None

    def calculate_indicators(self, df):
        if len(df) < BB_LENGTH:
            logging.warning("Not enough data to calculate indicators.")
            return None
        df.ta.bbands(append=True, length=BB_LENGTH, std=BB_STD)
        df.ta.rsi(append=True, length=RSI_LENGTH)
        df.rename(columns={f'BBL_{BB_LENGTH}_{BB_STD}.0': 'bbl', f'BBU_{BB_LENGTH}_{BB_STD}.0': 'bbh'}, inplace=True)
        return df

    def signal_checker(self, df):
        if df is None or df.empty or 'bbl' not in df.columns:
            return 0
        latest_candle = df.iloc[-1]
        if latest_candle['Close'] < latest_candle['bbl']:
            return 1  # buy signal
        elif latest_candle['Close'] > latest_candle['bbh']:
            return 2  # sell signal
        return 0  # side-trend or no signal

    @retry_on_error(max_retries=3, base_delay=0.5, max_delay=10.0)
    def check_open_trades(self, first_run=False):
        """
        Fetches open trades and stores their actual execution prices for grid calculations.
        Uses actual execution prices (not intended grid prices) for all grid calculations.
        """
        try:
            r = trades.OpenTrades(accountID=self.account_ID)
            open_trades = self.api.request(r)
            self.open_positions = {'buy': [], 'sell': []}
            # Collect all open positions with their actual execution prices
            for trade in open_trades.get('trades', []):
                if trade.get('instrument') == self.instrument:
                    units = int(trade['currentUnits'])
                    price = float(trade['price'])  # Actual execution price
                    trade_id = trade['id']
                    # Store positions with actual execution prices for grid calculations
                    if units > 0:
                        self.open_positions['buy'].append({'id': trade_id, 'units': units, 'price': price})
                    elif units < 0:
                        self.open_positions['sell'].append({'id': trade_id, 'units': abs(units), 'price': price})
            # Calculate and apply TPs based on actual execution prices (NO SL)
            if first_run:
                # Handle buy positions
                if self.open_positions['buy']:
                    # Sort by actual execution price ascending to find lowest price
                    sorted_buys = sorted(self.open_positions['buy'], key=lambda x: x['price'])
                    lowest_price = sorted_buys[0]['price']
                    # Calculate next grid based on actual execution price
                    next_grid = lowest_price - self.grid_distance_pips * self.pip_location
                    logging.info(f"Next BUY grid level will be at: {next_grid:.{self.instrument_precision}f}")
                    # Only log to file, do not print to screen
                    logging.info(f"OANDA account has open BUY positions: {len(self.open_positions['buy'])}")
                    # Always recalculate TP for existing positions (single or multiple)
                    self.update_collective_tp('buy')
                # Handle sell positions
                if self.open_positions['sell']:
                    # Sort by actual execution price descending to find highest price
                    sorted_sells = sorted(self.open_positions['sell'], key=lambda x: x['price'], reverse=True)
                    highest_price = sorted_sells[0]['price']
                    # Calculate next grid based on actual execution price
                    next_grid = highest_price + self.grid_distance_pips * self.pip_location
                    logging.info(f"Next SELL grid level will be at: {next_grid:.{self.instrument_precision}f}")
                    # Only log to file, do not print to screen
                    logging.info(f"OANDA account has open SELL positions: {len(self.open_positions['sell'])}")
                    # Always recalculate TP for existing positions (single or multiple)
                    self.update_collective_tp('sell')
        except Exception as e:
            logging.error(f"Error fetching open trades: {e}")
            # Only reset positions on first run or if we have no existing data
            # This prevents duplicate position opening when temporary connection errors occur
            if first_run or not any(self.open_positions.values()):
                self.open_positions = {'buy': [], 'sell': []}
            # For connection errors during normal operation, preserve existing position data
            # to prevent opening duplicate positions

    def check_open_trades_silent(self):
        """
        Silent version of check_open_trades that only updates positions without logging.
        Used for internal checks like when resetting financing adjustments.
        """
        try:
            r = trades.OpenTrades(accountID=self.account_ID)
            open_trades = self.api.request(r)
            self.open_positions = {'buy': [], 'sell': []}
            
            for trade in open_trades.get('trades', []):
                if trade.get('instrument') == self.instrument:
                    units = int(trade['currentUnits'])
                    price = float(trade['price'])
                    trade_id = trade['id']
                    
                    if units > 0:
                        self.open_positions['buy'].append({'id': trade_id, 'units': units, 'price': price})
                    elif units < 0:
                        self.open_positions['sell'].append({'id': trade_id, 'units': abs(units), 'price': price})
                        
        except Exception as e:
            logging.warning(f"Silent trade check failed: {e}")

    @retry_on_error(max_retries=3, base_delay=1.0, max_delay=20.0)
    def place_market_order(self, units, tp_price=None, intended_grid_price=None):
        """
        Place market order with TP only - NO SL
        """
        # Determine direction first
        direction = 'BUY' if int(units) > 0 else 'SELL'

        data = {
            "order": {
                "instrument": self.instrument,
                "units": str(units),
                "type": "MARKET",
                "positionFill": "OPEN_ONLY"
            }
        }
        if tp_price:
            data['order']['takeProfitOnFill'] = {"price": "{:.{prec}f}".format(tp_price, prec=self.instrument_precision)}
        
        # Store intended_grid_price in both comment and tag for robustness
        if intended_grid_price is not None:
            data['order']['clientExtensions'] = {
                "comment": f"grid:{intended_grid_price}",
                "tag": f"grid:{intended_grid_price}",
                "id": f"grid_{direction}_{intended_grid_price}"
            }
        try:
            r = orders.OrderCreate(self.account_ID, data=data)
            response = self.api.request(r)
            tp_str = f"{tp_price:.{self.instrument_precision}f}" if tp_price is not None else "None"
            logging.info(f"New position opened: {direction}, size: {abs(units)}, TP: {tp_str}, SL: DISABLED")
            return response
        except Exception as e:
            logging.error(f"❌ Error placing order: {e}")
            return None

    def update_trade_orders(self, trade_id, tp_price=None, skip_tp=False):
        """
        Updates TP on an existing trade - NO SL LOGIC
        """
        data = {}
        if tp_price and not skip_tp:
            tp_formatted = "{:.{prec}f}".format(tp_price, prec=self.instrument_precision)
            data['takeProfit'] = {"price": tp_formatted}
        if not data:
            return
        try:
            r = trades.TradeCRCDO(accountID=self.account_ID, tradeID=trade_id, data=data)
            self.api.request(r)
            # Only log if we actually made changes
            if 'takeProfit' in data:
                logging.info(f"Updated orders for trade {trade_id}: TP={tp_formatted}")
        except Exception as e:
            logging.error(f"Error updating orders for trade {trade_id}: {e}")

    def get_next_martingale_units(self, direction):
        idx = len(self.open_positions[direction])
        lot_size = self.martingale_sequence[idx] if idx < len(self.martingale_sequence) else self.martingale_sequence[-1]
        return int(lot_size * 100_000)

    def get_next_grid_price(self, direction):
        """Calculate next grid level based on the actual execution price of the last position"""
        grid = self.open_positions[direction]
        if not grid:
            return None
            
        # Find most extreme price from actual filled positions
        if direction == 'buy':
            last_price = min(pos['price'] for pos in grid)  # Lowest actual price for buys
        else:
            last_price = max(pos['price'] for pos in grid)  # Highest actual price for sells
        
        # Calculate next grid price based on direction
        if direction == 'buy':
            return last_price - self.grid_distance_pips * self.pip_location
        else:
            return last_price + self.grid_distance_pips * self.pip_location

    def check_grid_condition(self, direction):
        if not self.open_positions[direction]:
            return False
        
        current_price = self.get_current_price()
        if current_price is None:
            return False
            
        next_grid_price = self.get_next_grid_price(direction)
        if next_grid_price is None:
            return False
        
        # For buy grids, only open when price is at or below the next grid price
        # For sell grids, only open when price is at or above the next grid price
        if direction == 'buy':
            return current_price <= next_grid_price
        else:
            return current_price >= next_grid_price

    @retry_on_error(max_retries=2, base_delay=0.5, max_delay=8.0)
    def get_current_price(self):
        candles = self.get_candles(2)
        if candles and len(candles) > 1:
            return float(str(candles[-1].bid.c))
        logging.error("Could not retrieve current price.")
        return None

    def get_dataframe_for_indicators(self, n=35):
        candles = self.get_candles(n)
        if candles:
            df = pd.DataFrame([{
                'Open': float(str(c.bid.o)),
                'Close': float(str(c.bid.c)),
                'High': float(str(c.bid.h)),
                'Low': float(str(c.bid.l))
            } for c in candles])
            return df
        return None

    @retry_on_error(max_retries=2, base_delay=1.0, max_delay=10.0)
    def get_account_balance(self):
        try:
            r = accounts.AccountDetails(self.account_ID)
            response = self.api.request(r)
            balance = float(response['account']['balance'])
            return balance
        except Exception as e:
            logging.error(f"Error fetching account balance: {e}")
            return None

    def get_pip_value(self):
        """
        Get pip value for the instrument. For EURUSD, 1 pip = $10 per lot. For JPY pairs, 1 pip = 1000 JPY per lot.
        Uses OANDA v20 InstrumentsDetails endpoint if possible, else falls back to config/default.
        """
        try:
            # OANDA v20 python package does NOT have InstrumentDetails endpoint, so always fallback
            raise AttributeError
        except Exception:
            # Do not log warning, just fallback
            return PIP_VALUE if PIP_VALUE is not None else 10.0

    def can_open_next_grid(self, direction):
        balance = self.get_account_balance()
        if balance is None:
            return False
        margin_rate = MARGIN_RATE
        required_margin_fraction = REQUIRED_MARGIN_FRACTION
        pip_value = self.get_pip_value()
        total_units = sum(trade['units'] for trade in self.open_positions[direction])
        next_units = self.get_next_martingale_units(direction)
        notional = (total_units + next_units)
        required_margin = notional * margin_rate
        # Only return False if margin is not enough, do not log warning
        return required_margin < required_margin_fraction * balance

    def check_financing_events(self):
        """
        Check for daily financing events from OANDA API.
        OANDA applies daily financing at 17:00 ET (21:00/22:00 UTC depending on DST).
        Only checks once per day when financing actually occurs.
        Always logs daily financing amount (even if 0.00).
        """
        now_utc = dt.datetime.now(dt.timezone.utc)
        today_str = now_utc.strftime('%Y-%m-%d')
        
        # Check if we already processed today's financing
        if today_str in self.daily_financing_history:
            return  # Already processed today's financing
        
        # Only check during financing window (20:00-23:59 UTC to account for DST variations)
        if not (20 <= now_utc.hour <= 23):
            return  # Not in financing window
            
        logging.info(f"🔍 Checking for daily financing events on {today_str}...")
        
        try:
            # Look for financing transactions from the last 24 hours
            since = (now_utc - dt.timedelta(hours=24)).strftime('%Y-%m-%dT%H:%M:%SZ')
            until = now_utc.strftime('%Y-%m-%dT%H:%M:%SZ')
            
            params = {
                "type": ["DAILY_FINANCING"],
                "instrument": self.instrument,
                "from": since,
                "to": until
            }
            r = transactions.TransactionHistory(self.account_ID, params=params)
            response = self.api.request(r)
            
            financing_total = 0.0
            financing_by_direction = {'buy': 0.0, 'sell': 0.0}
            financing_found = False
            
            # Process all financing transactions for today
            for tx in response.get('transactions', []):
                if tx['type'] == 'DAILY_FINANCING':
                    tx_time = dt.datetime.strptime(tx['time'][:19], "%Y-%m-%dT%H:%M:%S")
                    tx_date = tx_time.strftime('%Y-%m-%d')
                    
                    # Only process today's transactions
                    if tx_date == today_str:
                        financing_found = True
                        financing = float(tx.get('financing', 0))
                        accountBalance = float(tx.get('accountBalance', 0))
                        units = int(tx.get('units', 0))
                        price = float(tx.get('price', 0)) if tx.get('price') else 0
                        
                        # Categorize by direction
                        direction = 'buy' if units > 0 else 'sell'
                        financing_by_direction[direction] += financing
                        financing_total += financing
                        
                        # Log detailed financing information
                        log_msg = (
                            f"💰 Daily Financing Transaction at {tx_time} UTC:\n"
                            f"   Amount: {financing:.2f} {self.quote_currency}\n"
                            f"   Account Balance: {accountBalance:.2f}\n"
                            f"   Direction: {direction.upper()}\n"
                            f"   Units: {units}, Price: {price:.{self.instrument_precision}f}\n"
                            f"   Instrument: {self.instrument}"
                        )
                        logging.info(log_msg)
            
            # Always log daily financing summary (even if 0.00)
            if financing_found or now_utc.hour >= 22:  # Log if found or after 22:00 UTC
                logging.info(f"📊 Daily Financing Summary for {today_str}:")
                logging.info(f"   Total: {financing_total:.2f} {self.quote_currency}")
                logging.info(f"   Buy positions: {financing_by_direction['buy']:.2f}")
                logging.info(f"   Sell positions: {financing_by_direction['sell']:.2f}")
                
                # Store financing data (even if zero)
                self.daily_financing_history[today_str] = financing_by_direction
                self.save_financing_data()
                
                # Apply financing to TP calculations if positions exist
                if any(self.open_positions[d] for d in ['buy', 'sell']):
                    logging.info("🔄 Updating TP calculations with daily financing data...")
                    self.recalculate_tp_with_real_financing(financing_by_direction)
                elif financing_total != 0:
                    logging.info("ℹ️  No open positions, but financing adjustments stored for future use")
                
        except Exception as e:
            logging.warning(f"Error checking financing transactions: {e}")
            # Still mark today as processed to avoid repeated API calls
            self.daily_financing_history[today_str] = {'buy': 0.0, 'sell': 0.0}

    def save_financing_data(self):
        """Save financing history to JSON file"""
        try:
            import json
            with open(self.financing_log_file, 'w') as f:
                json.dump(self.daily_financing_history, f, indent=2)
        except Exception as e:
            logging.warning(f"Could not save financing data: {e}")

    def load_financing_data(self):
        """Load financing history from JSON file"""
        try:
            import json
            if os.path.exists(self.financing_log_file):
                with open(self.financing_log_file, 'r') as f:
                    self.daily_financing_history = json.load(f)
        except Exception as e:
            logging.warning(f"Could not load financing data: {e}")
            self.daily_financing_history = {}

    def recalculate_tp_with_real_financing(self, financing_amounts):
        """
        Integrate actual daily financing amounts into TP calculations.
        The financing cost/gain is factored into the £1.50 per 0.01 lots profit target.
        
        Logic:
        - If financing is negative (cost): increase TP distance to compensate
        - If financing is positive (gain): can reduce TP distance slightly
        - Financing is applied per lot, scaled by position size
        """
        for direction in ['buy', 'sell']:
            if not self.open_positions[direction]:
                continue
                
            actual_financing = financing_amounts.get(direction, 0)
            total_units = sum(trade['units'] for trade in self.open_positions[direction])
            total_lots = total_units / 100_000
            
            # Calculate financing impact per lot
            financing_per_lot = actual_financing / total_lots if total_lots > 0 else 0
            
            logging.info(f"📊 {direction.upper()} financing analysis:")
            logging.info(f"   Daily financing: {actual_financing:.2f} {self.quote_currency}")
            logging.info(f"   Position size: {total_lots:.3f} lots ({total_units} units)")
            logging.info(f"   Financing per lot: {financing_per_lot:.2f} {self.quote_currency}")
            
            if total_lots > 0:
                # Convert financing to GBP (account currency)
                financing_per_lot_gbp = financing_per_lot * self.quote_to_account_rate
                
                # Our profit target is £1.50 per 0.01 lots = £150 per full lot
                # Adjust the target to account for financing
                base_profit_target_per_lot = self.profit_target_per_lot  # £150 per lot
                
                # If financing is negative (cost), we need higher profit to compensate
                # If financing is positive (gain), we can accept slightly lower profit
                adjusted_profit_target_per_lot = base_profit_target_per_lot - financing_per_lot_gbp
                
                # Calculate the adjustment factor
                adjustment_factor = adjusted_profit_target_per_lot / base_profit_target_per_lot
                
                logging.info(f"   Financing per lot (GBP): £{financing_per_lot_gbp:.2f}")
                logging.info(f"   Base profit target: £{base_profit_target_per_lot:.2f} per lot")
                logging.info(f"   Adjusted profit target: £{adjusted_profit_target_per_lot:.2f} per lot")
                logging.info(f"   TP adjustment factor: {adjustment_factor:.4f}")
                
                # Store the financing adjustment for this direction
                # This will be used in calculate_profit_based_tp to modify the target
                self.financing_adjustment[direction] = adjustment_factor - 1.0  # Store as percentage change
                
                logging.info(f"   Applied financing adjustment: {self.financing_adjustment[direction]:+.4f} ({self.financing_adjustment[direction]*100:+.2f}%)")
                
                # Recalculate collective TP with financing-adjusted profit target
                self.update_collective_tp(direction)
            else:
                # Reset adjustment if no positions
                self.financing_adjustment[direction] = 0.0

    def initialize_grids(self):
        """
        On startup, fetch open trades, calculate and set SL, TP, and grid for all open positions.
        Log open trades count if any are found.
        """
        self.check_open_trades(first_run=True)
        for direction in ['buy', 'sell']:
            if self.open_positions[direction]:
                logging.info(f"[STARTUP] OANDA account has open {direction.upper()} positions: {len(self.open_positions[direction])}")
        self.initialized = True

    def is_in_rollover_block(self):
        """
        Returns True if current UTC time is within the restricted rollover window (from config).
        """
        start = dt.datetime.strptime(ROLLOVER_BLOCK_START, '%H:%M').time()
        end = dt.datetime.strptime(ROLLOVER_BLOCK_END, '%H:%M').time()
        now = dt.datetime.now(dt.timezone.utc).time()  # Use timezone-aware UTC
        if start < end:
            return start <= now < end
        else:
            # Window spans midnight
            return now >= start or now < end

    def run(self):
        # Only initialize once at startup
        if not self.initialized:
            self.initialize_grids()
            return  # Wait for next tick to proceed

        # === DEBUG STATUS CHECK ===
        # For debugging purposes: Print periodic status every 6 hours
        self.check_and_print_debug_status()

        # === FINANCING EVENTS CHECK ===
        # Check for actual daily financing events around 22:00 UTC
        self.check_financing_events()

        # Block new trades during rollover window
        if self.is_in_rollover_block():
            return

        price = self.get_current_price()
        if price is None:
            self.log_debug_signals(None, None, 0)  # Log even if price fetch fails
            return
        df = self.get_dataframe_for_indicators()
        if df is None:
            self.log_debug_signals(None, price, 0)  # Log even if indicator fetch fails
            return
        df = self.calculate_indicators(df)
        signal = self.signal_checker(df)
        self.log_debug_signals(df, price, signal)  # Log every tick

        # --- Always check BBands for initial signal if no positions open ---
        if not self.open_positions['buy'] and not self.open_positions['sell']:
            if signal == 1:
                logging.info("Signal to open initial BUY.")
                units = self.get_next_martingale_units('buy')
                tp_price = self.calculate_initial_tp('buy', units, price)
                tp_price = self.adjust_tp_for_swap('buy', tp_price)
                # Calculate TP info for logging
                if tp_price is not None:
                    pips = abs(tp_price - price) / self.pip_location
                    amount = self.profit_target_per_lot * (abs(units) / 100_000)
                    logging.info(f"OPEN BUY: size={units}, price={price:.{self.instrument_precision}f}, SL=DISABLED, TP={tp_price:.{self.instrument_precision}f} (Target £{amount:.2f}, {pips:.1f} pips)")
                else:
                    logging.info(f"OPEN BUY: size={units}, price={price:.{self.instrument_precision}f}, SL=DISABLED, TP=None")
                self.log_debug_signals(df, price, signal, action="OPEN BUY")
                self.place_market_order(units, tp_price, intended_grid_price=round(price, self.instrument_precision))
                self.check_open_trades()  # Fetch new trade info
                self.update_collective_tp('buy')
                next_grid_price = price - self.grid_distance_pips * self.pip_location
                logging.info(f"Next BUY grid price: {next_grid_price:.{self.instrument_precision}f}")
            elif signal == 2:
                logging.info("Signal to open initial SELL.")
                units = self.get_next_martingale_units('sell')
                tp_price = self.calculate_initial_tp('sell', units, price)
                tp_price = self.adjust_tp_for_swap('sell', tp_price)
                if tp_price is not None:
                    pips = abs(tp_price - price) / self.pip_location
                    amount = self.profit_target_per_lot * (abs(units) / 100_000)
                    logging.info(f"OPEN SELL: size={units}, price={price:.{self.instrument_precision}f}, SL=DISABLED, TP={tp_price:.{self.instrument_precision}f} (Target £{amount:.2f}, {pips:.1f} pips)")
                else:
                    logging.info(f"OPEN SELL: size={units}, price={price:.{self.instrument_precision}f}, SL=DISABLED, TP=None")
                self.log_debug_signals(df, price, signal, action="OPEN SELL")
                self.place_market_order(-units, tp_price, intended_grid_price=round(price, self.instrument_precision))
                self.check_open_trades()  # Fetch new trade info
                self.update_collective_tp('sell')
                next_grid_price = price + self.grid_distance_pips * self.pip_location
                logging.info(f"Next SELL grid price: {next_grid_price:.{self.instrument_precision}f}")
        else:
            # CRITICAL: Refresh positions before grid logic to ensure accuracy after TP closures
            self.check_open_trades()
            
            # If buy grid open, check grid logic for buy
            if self.open_positions['buy']:
                next_grid_price = self.get_next_grid_price('buy')
                if self.check_grid_condition('buy') and self.can_open_next_grid('buy'):
                    units = self.get_next_martingale_units('buy')
                    tp_price = self.adjust_tp_for_swap('buy', None)
                    if tp_price is not None:
                        pips = abs(tp_price - next_grid_price) / self.pip_location
                        amount = self.profit_target_per_lot * (abs(units) / 100_000)
                        logging.info(f"OPEN BUY GRID: size={units}, price={next_grid_price:.{self.instrument_precision}f}, SL=DISABLED, TP={tp_price:.{self.instrument_precision}f} (Target £{amount:.2f}, {pips:.1f} pips)")
                    else:
                        logging.info(f"OPEN BUY GRID: size={units}, price={next_grid_price:.{self.instrument_precision}f}, SL=DISABLED, TP=None")
                    self.log_debug_signals(df, next_grid_price, signal, action="OPEN BUY GRID")
                    
                    # Track position count before placing order
                    current_count = len(self.open_positions['buy'])
                    self.place_market_order(units, tp_price, intended_grid_price=round(next_grid_price, self.instrument_precision))
                    # Wait for the new position to appear
                    for _ in range(10):
                        sleep(0.2)
                        self.check_open_trades()
                        if len(self.open_positions['buy']) > current_count:
                            break
                    self.update_collective_tp('buy')
                    next_grid_price = self.get_next_grid_price('buy')
                    logging.info(f"Next BUY grid price: {next_grid_price:.{self.instrument_precision}f}")
            # If sell grid open, check grid logic for sell
            if self.open_positions['sell']:
                next_grid_price = self.get_next_grid_price('sell')
                if self.check_grid_condition('sell') and self.can_open_next_grid('sell'):
                    units = self.get_next_martingale_units('sell')
                    grid_price = self.get_next_grid_price('sell')
                    tp_price = self.adjust_tp_for_swap('sell', None)
                    if tp_price is not None:
                        pips = abs(tp_price - grid_price) / self.pip_location
                        amount = self.profit_target_per_lot * (abs(units) / 100_000)
                        logging.info(f"OPEN SELL GRID: size={units}, price={grid_price:.{self.instrument_precision}f}, SL=DISABLED, TP={tp_price:.{self.instrument_precision}f} (Target £{amount:.2f}, {pips:.1f} pips)")
                    else:
                        logging.info(f"OPEN SELL GRID: size={units}, price={grid_price:.{self.instrument_precision}f}, SL=DISABLED, TP=None")
                    self.log_debug_signals(df, grid_price, signal, action="OPEN SELL GRID")
                    # Track position count before placing order
                    current_count = len(self.open_positions['sell'])
                    self.place_market_order(-units, tp_price, intended_grid_price=round(grid_price, self.instrument_precision))
                    # Wait for the new position to appear
                    for _ in range(10):
                        sleep(0.2)
                        self.check_open_trades()
                        if len(self.open_positions['sell']) > current_count:
                            break
                    self.update_collective_tp('sell')
                    next_grid_price = self.get_next_grid_price('sell')
                    logging.info(f"Next SELL grid price: {next_grid_price:.{self.instrument_precision}f}")
        # Log closed trades at the end of each run
        self.log_closed_trades()

    def log_closed_trades(self):
        """
        Log only trades that have just closed (TP/SL), at the exact moment of closure.
        Only log if any trades have actually closed.
        """
        try:
            r = trades.OpenTrades(accountID=self.account_ID)
            open_trades = self.api.request(r)
            current_open_ids = set()
            for trade in open_trades.get('trades', []):
                if trade.get('instrument') == self.instrument:
                    current_open_ids.add(str(trade['id']))
            if not hasattr(self, 'prev_open_trade_ids') or self.prev_open_trade_ids is None:
                self._save_last_open_trade_ids(list(current_open_ids))
                self.prev_open_trade_ids = current_open_ids
                return
            just_closed_ids = self.prev_open_trade_ids - current_open_ids
            if not just_closed_ids:
                return  # No closed trades, avoid log spam
            for closed_id in just_closed_ids:
                r = trades.TradeDetails(self.account_ID, closed_id)
                try:
                    trade_details = self.api.request(r)
                    trade = trade_details['trade']
                    realized_pl = float(trade.get('realizedPL', 0))
                    swap = float(trade.get('financing', 0))
                    open_time = trade.get('openTime')
                    close_time = trade.get('closeTime')
                    reason = trade.get('closeReason', '')
                    if not reason:
                        last_tx_id = trade.get('lastTransactionID')
                        if last_tx_id is not None and str(last_tx_id).lower() != 'none':
                            rtx = transactions.TransactionDetails(self.account_ID, last_tx_id)
                            try:
                                tx = self.api.request(rtx).get('transaction', {})
                                reason = tx.get('reason', '')
                            except Exception as e:
                                logging.warning(f"Could not fetch transaction details for trade {closed_id}: {e}")
                        else:
                            reason = ''
                    held_overnight = False
                    if open_time and close_time:
                        open_dt = dt.datetime.strptime(open_time[:19], "%Y-%m-%dT%H:%M:%S")
                        close_dt = dt.datetime.strptime(close_time[:19], "%Y-%m-%dT%H:%M:%S")
                        held_overnight = (close_dt.date() > open_dt.date()) and (close_dt.hour >= 21)
                    total_pl = realized_pl + (swap if held_overnight else 0)
                    # Map OANDA reason to human-readable, improve TP/CLOSE logic
                    if reason in ['TAKE_PROFIT_ORDER', 'MARKET_TAKE_PROFIT', 'TP']:
                        reason_str = 'TP'
                    elif reason in ['STOP_LOSS_ORDER', 'MARKET_STOP_LOSS', 'SL']:
                        reason_str = 'SL'
                    elif reason == 'CLOSE':
                        # If realized profit is positive, treat as TP; if negative, treat as CLOSE
                        if realized_pl > 0:
                            reason_str = 'TP'
                        elif realized_pl < 0:
                            reason_str = 'CLOSE'
                        else:
                            reason_str = 'CLOSE'
                    elif reason:
                        reason_str = reason
                    else:
                        reason_str = 'CLOSE'
                    logging.info(f"Position {closed_id} closed by {reason_str}: Net P/L £{total_pl:.2f} (Realized: £{realized_pl:.2f}, Swap: £{swap if held_overnight else 0:.2f}){' [overnight]' if held_overnight else ''}")
                except Exception as e:
                    logging.error(f"Error fetching closed trade details for {closed_id}: {e}")
            self._save_last_open_trade_ids(list(current_open_ids))
            self.prev_open_trade_ids = current_open_ids
            
            # Check if any grids are now completely closed and reset financing adjustments
            current_positions_after_closure = self.check_open_trades_silent()
            for direction in ['buy', 'sell']:
                # If a grid is now empty and had financing adjustments, reset them
                if not self.open_positions[direction] and self.financing_adjustment[direction] != 0:
                    self.reset_financing_adjustments(direction)
                    
        except Exception as e:
            logging.error(f"Error in live closed trade logging: {e}")

    def get_swap_rates(self):
        """
        Only use swap rates from config SWAP_INFO.
        """
        return SWAP_INFO.get(self.instrument, {"long": 0.0, "short": 0.0, "triple_day": "Wednesday"})

    def is_duplicate_grid(self, direction, intended_grid_price):
        """Legacy method, left empty for compatibility"""
        return False

    def open_grid_position(self, direction):
        # Get next intended grid price
        next_grid_price = self.get_next_grid_price(direction)
        if next_grid_price is None:
            return
        # Check for duplicate
        if self.is_duplicate_grid(direction, next_grid_price):
            logging.info(f"Duplicate {direction.upper()} grid at {next_grid_price}, skipping.")
            return
        # Calculate order size
        size = self.grid_size
        if direction == 'sell':
            size = -size
        # Place order with intended_grid_price
        self.place_market_order(size, intended_grid_price=next_grid_price)
        logging.info(f"OPEN {direction.upper()} GRID: size={abs(size)}, intended_grid_price={next_grid_price}")

    def validate_grid_progression(self, direction):
        """Legacy method, left empty for compatibility"""
        return True

    def calculate_initial_tp(self, direction, units, entry_price):
        """Calculate TP for initial position based on profit target with proper fallback hierarchy"""
        # Convert units to lots
        lots = abs(units) / 100_000
        profit_target = self.profit_target_per_lot * lots
        
        # Fallback hierarchy for TP calculation:
        # 1. Profit-based TP using startup exchange rate
        # 2. Fixed pip distance from config (TP_PIPS)
        # 3. Hardcoded pip values from config (FALLBACK_PIP_VALUES)
        
        # Attempt 1: Profit-based TP calculation using startup rate
        try:
            # Get dynamic pip value based on instrument
            pip_value_location = self.get_pip_value_for_instrument()
            
            # Calculate required pips for target profit
            pip_value_in_quote = pip_value_location * abs(units)  # One pip value in quote currency
            pip_value_in_gbp = pip_value_in_quote * self.quote_to_account_rate
            
            if pip_value_in_gbp > 0:
                required_pips = profit_target / pip_value_in_gbp
                tp_distance = required_pips * pip_value_location
                tp_price = entry_price + (tp_distance if direction == 'buy' else -tp_distance)
                
                logging.info(f"Profit-based TP: Target=£{profit_target:.2f}, "
                           f"Required Pips={required_pips:.1f}, Entry={entry_price:.5f}, TP={tp_price:.5f}")
                return tp_price
            else:
                raise ValueError("Invalid pip value calculation")
                
        except Exception as e:
            logging.warning(f"Profit-based TP calculation failed: {e}")
        
        # Fallback 2: Fixed pip distance from config
        try:
            pip_value_location = self.get_pip_value_for_instrument()
            tp_distance = self.tp_pips * pip_value_location
            tp_price = entry_price + (tp_distance if direction == 'buy' else -tp_distance)
            
            logging.info(f"Fixed pip TP fallback: TP_PIPS={self.tp_pips}, "
                        f"Entry={entry_price:.5f}, TP={tp_price:.5f}")
            return tp_price
            
        except Exception as e:
            logging.warning(f"Fixed pip TP calculation failed: {e}")
        
        # Fallback 3: Hardcoded pip values from config
        try:
            if self.instrument in self.fallback_pip_values:
                pip_value_location = self.fallback_pip_values[self.instrument]
            else:
                pip_value_location = 0.0001  # Default for most major pairs
                
            tp_distance = self.tp_pips * pip_value_location
            tp_price = entry_price + (tp_distance if direction == 'buy' else -tp_distance)
            
            logging.warning(f"Using hardcoded pip value fallback: pip_location={pip_value_location}, "
                          f"Entry={entry_price:.5f}, TP={tp_price:.5f}")
            return tp_price
            
        except Exception as e:
            logging.error(f"All TP calculation methods failed: {e}")
            # Last resort: use current pip_location from config
            tp_distance = self.tp_pips * self.pip_location
            tp_price = entry_price + (tp_distance if direction == 'buy' else -tp_distance)
            return tp_price
    
    def get_pip_value_for_instrument(self):
        """Get pip value for the current instrument with fallback to config"""
        # First try to get from fallback config
        if self.instrument in self.fallback_pip_values:
            return self.fallback_pip_values[self.instrument]
        
        # If not in config, use the PIP_LOCATION from config
        return self.pip_location

    def adjust_tp_for_swap(self, direction, tp_price):
        """
        Adjusts the TP price for swap/financing if needed. Currently returns TP unchanged.
        If tp_price is None, recalculates the collective TP for the direction (for grid logic).
        """
        if tp_price is None:
            # Recalculate collective TP for the grid
            return self.calculate_profit_based_tp(direction, self.open_positions[direction])
        return tp_price

    def update_collective_tp(self, direction):
        """
        Updates collective TP for existing grid positions using profit-based calculation.
        This is called at startup and during operation when grid positions change.
        """
        grid = self.open_positions[direction]
        if len(grid) < 2:
            # For single positions, calculate individual TP
            if len(grid) == 1:
                trade = grid[0]
                units = trade['units'] if direction == 'buy' else -trade['units']
                tp_price = self.calculate_initial_tp(direction, units, trade['price'])
                if tp_price:
                    self.update_trade_orders(trade['id'], tp_price=tp_price)
                    logging.info(f"Updated single {direction} position TP to {tp_price:.5f}")
            return

        # For grids with 2+ positions, use profit-based collective TP
        new_tp = self.calculate_profit_based_tp(direction, grid)
        if new_tp is None:
            logging.warning(f"Could not calculate profit-based TP for {direction} grid, falling back to pip-based")
            # Fallback to old VWAP + pip distance method
            total_units = sum(trade['units'] for trade in grid)
            vwap_numerator = sum(trade['price'] * trade['units'] for trade in grid)
            if total_units == 0:
                return
            break_even_price = vwap_numerator / total_units
            if direction == 'buy':
                new_tp = break_even_price + self.grid_tp_pips * self.pip_location
            else:
                new_tp = break_even_price - self.grid_tp_pips * self.pip_location

        tp_formatted = float("{:.{prec}f}".format(new_tp, prec=self.instrument_precision))
        # Only update if TP changed significantly (tolerance for float rounding)
        if self.last_collective_tp[direction] is None or abs(self.last_collective_tp[direction] - tp_formatted) > 1e-6:
            financing_info = ""
            if hasattr(self, 'financing_adjustment') and self.financing_adjustment.get(direction) is not None:
                financing_adj_pct = self.financing_adjustment[direction] * 100
                financing_info = f" (financing adj: {financing_adj_pct:+.2f}%)"
            logging.info(f"[STARTUP] Updating collective TP for {direction} grid to: {tp_formatted}{financing_info}")
            self.last_collective_tp[direction] = tp_formatted
            # Update all trades in this grid
            for trade in grid:
                self.update_trade_orders(trade['id'], tp_price=tp_formatted)

    # === DEBUG STATUS REPORTING ===
    def check_and_print_debug_status(self):
        """
        FOR DEBUGGING PURPOSES ONLY: Print bot status every 6 hours to confirm:
        - Bot is still online and connected
        - Can fetch live data from OANDA
        - Current grid positions and next intended levels
        - Live price and signal information
        """
        global DEBUG_LAST_STATUS_TIME
        current_time = dt.datetime.now(dt.timezone.utc)
        if (DEBUG_LAST_STATUS_TIME is None or 
            (current_time - DEBUG_LAST_STATUS_TIME).total_seconds() >= DEBUG_STATUS_INTERVAL_HOURS * 3600):
            DEBUG_LAST_STATUS_TIME = current_time
            try:
                current_price = self.get_current_price()
                df = self.get_dataframe_for_indicators()
                signal = 0
                bb_lower = bb_upper = None
                if df is not None and not df.empty:
                    # Calculate indicators to get BBands
                    df_with_indicators = self.calculate_indicators(df)
                    if df_with_indicators is not None and 'bbl' in df_with_indicators.columns and 'bbh' in df_with_indicators.columns:
                        bb_lower = df_with_indicators.iloc[-1]['bbl']
                        bb_upper = df_with_indicators.iloc[-1]['bbh']
                    signal = self.signal_checker(df_with_indicators)
                signal_text = {0: "NO SIGNAL", 1: "BUY SIGNAL", 2: "SELL SIGNAL"}.get(signal, "UNKNOWN")
                buy_positions = len(self.open_positions.get('buy', []))
                sell_positions = len(self.open_positions.get('sell', []))
                next_buy_grid = self.get_next_grid_price('buy') if buy_positions > 0 else None
                next_sell_grid = self.get_next_grid_price('sell') if sell_positions > 0 else None
                
                # Format grid prices with instrument precision
                next_buy_grid_formatted = f"{next_buy_grid:.{self.instrument_precision}f}" if next_buy_grid is not None else None
                next_sell_grid_formatted = f"{next_sell_grid:.{self.instrument_precision}f}" if next_sell_grid is not None else None
                
                # Format BB values with reasonable precision
                bb_lower_formatted = f"{bb_lower:.{self.instrument_precision}f}" if bb_lower is not None else None
                bb_upper_formatted = f"{bb_upper:.{self.instrument_precision}f}" if bb_upper is not None else None
                
                status_block = (
                    f"\n🔄 [DEBUG-STATUS] Bot1v5 Online Check - {current_time.strftime('%Y-%m-%d %H:%M:%S UTC')}\n"
                    f"   💰 {self.instrument}: Current Price = {current_price}\n"
                    f"   📊 Signal: {signal_text} | BB Lower: {bb_lower_formatted} | BB Upper: {bb_upper_formatted}\n"
                    f"   📈 Positions: {buy_positions} BUY, {sell_positions} SELL | Next BUY grid: {next_buy_grid_formatted} | Next SELL grid: {next_sell_grid_formatted}\n"
                    f"   ✅ OANDA Connection: OK | Data Fetch: OK | Bot Status: ONLINE\n"
                )
                # Print status to console (not file)
                print(status_block)
            except Exception as e:
                print(f"[DEBUG STATUS] Error during status check: {e}")

    # === DEBUG SIGNAL LOGGING ===
    def log_debug_signals(self, df, current_price, signal, action=None):
        """
        Log BBands, current price, and signal every minute for debugging.
        If a position is opened, log the action as well.
        """
        try:
            bb_lower = bb_upper = None
            if df is not None and not df.empty:
                if 'bbl' in df.columns and 'bbh' in df.columns:
                    bb_lower = df.iloc[-1]['bbl']
                    bb_upper = df.iloc[-1]['bbh']
            signal_text = {0: "NO SIGNAL", 1: "BUY SIGNAL", 2: "SELL SIGNAL"}.get(signal, "UNKNOWN")
            msg = f"BBL={bb_lower}, BBH={bb_upper}, Price={current_price}, Signal={signal_text}"
            if action:
                msg += f", Action={action}"
            debug_logger.info(msg)
        except Exception as e:
            debug_logger.error(f"[DEBUG SIGNALS] Error logging debug signals: {e}")

    def reset_financing_adjustments(self, direction=None):
        """
        Reset financing adjustments for specified direction or all directions.
        Called when grids are closed or when starting fresh calculations.
        """
        if direction:
            self.financing_adjustment[direction] = 0
            logging.info(f"Reset financing adjustment for {direction} direction")
        else:
            self.financing_adjustment = {'buy': 0, 'sell': 0}
            logging.info("Reset all financing adjustments")

def start_scheduler():
    scheduler = BackgroundScheduler(timezone="UTC")
    bot = TradingBot()
    #bot.check_open_trades(first_run=True)
    # Use config settings instead of hardcoded values
    interval_secs = BOT_INTERVAL
    mode = "test" if interval_secs <= 5 else "live"
    timeframe_str = f"{CANDLE_TIMEFRAME}"
    scheduler.add_job(bot.run, 'interval', seconds=interval_secs)
    print(f"🤖 Starting the trading bot ({mode} mode, {PAIR}, {timeframe_str}, {interval_secs}s interval) - Press CTRL+C to stop.")
    try:
        scheduler.start()
        while True:
            sleep(1)
    except KeyboardInterrupt:
        print("\n🛑 Stopping the bot...")
        scheduler.shutdown(wait=False)  # Don't wait for jobs to complete

if __name__ == "__main__":
    start_scheduler()
