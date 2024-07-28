import Peripherals

def Colors.white : Color := { red := 0xFF, green := 130, blue := 220 }
def Colors.red : Color := { red := 0xFF, green := 0, blue := 0 }
def Colors.green : Color := { red := 0, green := 0xFF, blue := 0 }
def Colors.blue : Color := { red := 0, green := 0, blue := 0xFF }

/-- Apply gamma correction to an intensity value so that it appears linear to the human eye. -/
def gamma (v : Fin 256) : UInt8 := (v.val * v.val / 255).toUInt8

-- PRNG based on:
-- https://gist.github.com/tommyettinger/46a874533244883189143505d203312c?permalink_comment_id=4365431#gistcomment-4365431
/-- The state of the pseudo random number generator.  -/
abbrev Prng.State := UInt32
/-- Advance the pseudo random number generator state to the next one. -/
def Prng.step (state : Prng.State) : Prng.State := state + 0x9E3779B9
/-- Get the current pseudo random number based on the state. -/
def Prng.get (z : Prng.State) : UInt32 :=
  let z := z ^^^ (z >>> 16)
  let z := z * 0x21F0AAAD
  let z := z ^^^ (z >>> 15)
  let z := z * 0x735A2D97
  z ^^^ (z >>> 15)

structure LightPattern where
  /-- Type of the inner state. -/
  State : Type
  /-- The initial state value. -/
  init : State
  /-- The function to advance the state. -/
  step : State → State
  /-- The function to get the current output color. -/
  color : State → Color

/-- Step `p` once every `n` steps. -/
def LightPattern.every (n : UInt16) (p : LightPattern) : LightPattern := {
  State := UInt16 × p.State,
  init := (0, p.init),
  step := fun (i, s) => if i == n then (0, p.step s) else (i + 1, s),
  color := fun (_, s) => p.color s
}

/-- Toggle on/off every step. -/
def LightPattern.blink (c : Color) : LightPattern := {
  State := Bool
  init := true
  step := Bool.not
  color := (if · then c else default)
}

/-- A candle-like flicker effect.  -/
def LightPattern.flicker : LightPattern := {
  State := Prng.State
  init := 0
  step := Prng.step
  color := fun state =>
    let random := Prng.get state
    let brighness := 0x80 + random &&& 0x7F
    {
      red := brighness.toUInt8,
      green := 150 * brighness / 255 |>.toUInt8,
      blue := 50 * brighness / 255 |>.toUInt8,
    }
}

inductive ColorChannel := | Red | Green | Blue
def ColorChannel.toColor (v : UInt8 := 0xFF) : ColorChannel → Color
| Red => { red := v, green := 0, blue := 0 }
| Green => { red := 0, green := v, blue := 0 }
| Blue => { red := 0, green := 0, blue := v }

/-- Cycle through the three primary colors. -/
def LightPattern.cycle : LightPattern := {
  State := ColorChannel
  init := .Red
  step := fun
    | .Red => .Green
    | .Green => .Blue
    | .Blue => .Red
  color := ColorChannel.toColor
}

/-- Ramp up to full brightness over `cycle` steps and back down again. -/
def LightPattern.breathe (cycle : UInt16) (c : ColorChannel) : LightPattern := {
  State := UInt16
  init := 0
  step := fun i => (i + 1) % (cycle * 2)
  color := fun i =>
    let f := if i < cycle then i else cycle * 2 - i
    let idx := f.toUInt32 * 256 / cycle.toUInt32
    c.toColor <| gamma <| Fin.ofNat idx.toNat
}

section AppState

-- Parameterize over an array of patterns.
variable (patterns : Array LightPattern)

structure AppState where
  /-- The index of the currently playing light pattern. -/
  patternIndex : Fin patterns.size
  /-- The current state of the light pattern, its type depends on the current index. -/
  state : (patterns.get patternIndex).State

/-- Switch to the next pattern. It will start playing from its initial state. -/
def AppState.nextPattern (s : AppState patterns) : AppState patterns :=
  let patternIndex := s.patternIndex + Fin.ofNat' 1 (
    match e : patterns.size with
    | 0 => Fin.elim0 (e ▸ s.patternIndex)
    | _ + 1 => (by omega))
  {
    patternIndex,
    state := (patterns.get patternIndex).init,
  }

/-- Update the state of the current pattern. -/
def AppState.step (s : AppState patterns) : AppState patterns :=
  { s with state := (patterns.get s.patternIndex).step s.state }

/-- Get the current output color. -/
def AppState.color (s : AppState patterns) : Color := (patterns.get s.patternIndex).color s.state

/-- Initialize a new app state. -/
def AppState.init (hPatterns : patterns.size > 0) : AppState patterns :=
  let patternIndex := Fin.ofNat' 0 hPatterns
  {
    patternIndex,
    state := (patterns.get patternIndex).init,
  }

end AppState

open LightPattern Colors in
/-- A collection of light patterns, assuming an update frequency of 1000Hz. -/
def patterns : Array LightPattern := #[
  every 500 (blink white),
  every 100 (blink white),
  every 500 (blink red),
  every 100 (blink red),
  every 500 (blink green),
  every 100 (blink green),
  every 500 (blink blue),
  every 100 (blink blue),

  every 500 cycle,
  every 100 cycle,

  every 50 flicker,

  breathe 1000 .Red,
  breathe 1000 .Green,
  breathe 1000 .Blue
]

def main : IO Unit := do
  IO.println "Hello from Lean main!"

  let mut appState : AppState patterns
    := AppState.init patterns (by simp [patterns])
  let mut buttonPressedPrev := false
  while true do
    -- Read the button state, advance to the next pattern when pressed
    let buttonPressed := !(← readGpio 9)
    if !buttonPressedPrev && buttonPressed then
      appState := appState.nextPattern
    buttonPressedPrev := buttonPressed

    -- Update the pattern state and output the current color to the LED
    appState := appState.step
    setLedState appState.color

    -- TODO:
    -- Use proper timer instead of just a wait, so the frequency does not
    -- depend on the time it takes to do the update.
    delayUs 1000
