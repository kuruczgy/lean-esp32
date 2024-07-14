
-- TODO: Override the default Nat repr instance with this.
/-- The default "fast" implementation in the Stdlib crashes, so use this instead. -/
def slowRepr (n : Nat) : String := (Nat.toDigits 10 n).asString

-- TODO: Only safe for scalar Nat
/-- Delay approximately by the given amount of microseconds. (Assuming 20MHz CPU clock.) -/
@[extern "c_delay_us"]
opaque delayUs : Nat → IO Unit

-- TODO: Does the lean IO abstraction not already have something like this?
/-- Flush stdout. -/
@[extern "c_flush"]
opaque flush : IO Unit

/-- Read the value of the given GPIO pin. -/
@[extern "c_read_gpio"]
opaque readGpio : Fin 22 → IO Bool

/-- An RGB color with 8 bit channels. -/
structure Color where
  red : UInt8
  green : UInt8
  blue : UInt8
deriving Inhabited

/-- Set the state of the LED. -/
@[extern "c_set_led_state"]
opaque setLedState : (@& Color) → IO Unit
