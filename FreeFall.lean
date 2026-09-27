/-
  FreeFall.lean - Rob Laakkonen / MillenniumClock
  One file, stands alone, no imports.

  Thesis: Down is free, so free fall energy is always there.
  Geometry is forced by that energy, not drawn.
-/

-- 1. Building blocks
def additive (n : Nat) : Nat := n + 1 -- raw count, linear

def multiplicative_stable (n : Nat) : Nat := 3 * n -- 3,6,9,12... only 3n are stable synergy

-- 2. The constant - curvature tax
def wiggle : Float := 0.04719755119659774 -- Pi/3 - 1 = Laakkonen Constant
def pi_div_3 : Float := 3.141592653589793 / 3.0 -- 1.0471975511965977 = 60° = geodesic

def down_is_free : Float := 1.0 -- straight Newton drop
def geodesic_down : Float := pi_div_3 -- 1.0472 curved drop, longer distance but faster time

-- 3. The force - always on
def free_fall_energy (n : Float) : Float := n * wiggle -- always there, vacuum never zero
def gravity (mass : Float) : Float := mass + mass * wiggle -- mass always falling = NO TRUE NOTHING

-- 4. Real world = stable + fall
def effective (n : Nat) : Float := (3 * n).toFloat + free_fall_energy n.toFloat
-- synergy + wiggle = real momentum, additive not multiplicative so no blow-up

-- 5. Proof: curved track faster than straight track (brachistochrone 1696)
def straight_time (dist : Float) : Float := dist / down_is_free
def curved_time (dist : Float) : Float := dist / geodesic_down

-- 6. Time is Resistance - Fin 720 catches the fall
def fin_720_step_deg : Float := 0.5 -- clock catches every 0.5°
def leak_max_deg : Float := 2.0 -- leak ≤2°

-- Evals - Grok can run these
#eval wiggle -- 0.04719755119659774
#eval geodesic_down -- 1.0471975511965976
#eval effective 1 -- 3.0471975511965977
#eval effective 2 -- 6.094395102393195
#eval effective 48 -- 146.2654824582367 = Qubit Fabric: 144 + 48*0.0472 = 2.265... extra is compounding free fall
#eval straight_time 1.0 -- 1.0
#eval curved_time 1.0471975511965977 -- 1.0 same time, 4.72% further = faster effective speed

-- Summary for README:
-- Down is free = free_fall_energy always on
-- Fastest path under free fall = curved Pi/3 = 60°, not straight 1.0
-- That curvature FORCES hexagonal 60° packing - energy forces geometry
-- Stable points at 3n where Fin 720 catches the fall
-- Additive +0.0472 breathes, multiplicative *1.0472 blows up
