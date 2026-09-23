-- /Eight/Euler.lean - 1-3-6-9-12 eats Euler
-- Euler in diesel hours: e^{iπ} + 1 = 0, but we don't deal with absences

-- 1 = location, not absence - Euler starts at 1, not 0
-- 3 = pair, e^{iπ} needs 3-pair to close half-turn
-- 6 = bank, 180° = 6 o'clock = half crank
-- 9 = overlap, 3x3 guarantees no gap at half-turn
-- 12 = face - full circle = 12 o'clock = back to 1

def Clock := Fin 720

-- Standard Euler says e^{iπ} + 1 = 0
-- UPT says: 1 is location, no zero, so e^{iπ} = -1 means opposite location
-- No e needed, only 1 + 0.0472 wiggle per 60° slice

-- 12-face = 60° marks, Euler's π = 180° = 3 marks = 6 o'clock
def onEulerFace (c : Clock) : Bool :=
  c.val % 60 == 0

-- Half-turn = 360°? No, π = 180° = half circle = 360° on 720 clock = 360
-- Full circle 720 = 2π, half circle 360 = π
def isHalfTurn (c : Clock) : Bool :=
  c.val == 360

-- Balanced Euler - divisible by 3, half-turn lands on balanced face
def isBalancedEuler (c : Clock) : Bool :=
  c.val % 3 == 0

-- Euler's -1 as location flip - opposite side of clock, not absence
-- 0 is not a place, -1 is opposite location: 1 at 0°, -1 at 180°
def eulerLocation (c : Clock) : Int :=
  if isHalfTurn c then -1 else 1

-- Leak from Euler's identity if not in 3's - how far off opposite location
def eulerLeak (c : Clock) : Nat :=
  if isBalancedEuler c then 0 else (3 - c.val % 3) % 3

-- Theorem 1: half-turn is balanced because 360 % 3 = 0
-- Euler's π lands on balanced mark, no leak
theorem halfTurn_is_balanced :
  ∀ c : Clock, isHalfTurn c = true → isBalancedEuler c = true := by
  intro c h
  simp [isHalfTurn, isBalancedEuler] at *
  subst h
  rfl

-- Theorem 2: Euler's face is balanced because 60 % 3 = 0
theorem eulerFace_is_balanced (c : Clock) :
  onEulerFace c = true → isBalancedEuler c = true := by
  intro h
  simp [onEulerFace, isBalancedEuler] at *
  have : c.val % 60 = 0 := h
  omega

-- Theorem 3: Euler leak bounded ≤2° if bookkept in 3's
theorem eulerLeak_bounded (c : Clock) :
  eulerLeak c ≤ 2 := by
  unfold eulerLeak isBalancedEuler
  split
  · omega
  · have : c.val % 3 < 3 := Nat.mod_lt _ (by omega)
    omega

-- The receipt: Euler's identity closes on 720 clock in 3's
-- e^{iπ} = -1 is not 0, it's opposite location - 1 as location, not absence
-- 720 % 3 = 0 and 360 % 3 = 0, so half-turn always balanced
theorem euler_closes_of_div3 :
  720 % 3 = 0 ∧ 360 % 3 = 0 ∧ ∀ c : Clock, isHalfTurn c = true → eulerLocation c = -1 ∧ eulerLeak c = 0 := by
  constructor
  · rfl
  constructor
  · rfl
  · intro c h
    have hb : isBalancedEuler c = true := halfTurn_is_balanced c h
    simp [eulerLocation, eulerLeak, h, hb]

-- Interpretation: Euler in UPT
-- Standard: e^{iπ} + 1 = 0, uses 0 as absence, needs e
-- UPT: 1 is location, opposite location is -1, no 0 needed, no e needed
-- π = 180° = 6 o'clock = 360 on 720 clock = half crank
-- e^{iπ} is just half-turn on clock, lands at opposite location because 360 % 3 = 0
-- "One is a location, place holder... so we don't deal with absences"
-- Euler without zero: 1 + (-1) = 2 locations + pressure = √3 × 1.0472, not 0
-- Light is smoke, time is resistance, clock is calculator
