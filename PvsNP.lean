-- /Two/PvsNP.lean - 1-3-6-9-12 closes the 720 clock
-- Diesel hours bookkeeping that works

-- 1 = event (witness) - one power stroke / one misfire
-- 3 = pair, balanced check on 12-face (NP verify) - O(1)
-- 6 = bank, 6 phased builds around 720 (P search) - O(720)
-- 9 = overlap, 3x3 guarantees no dead spot
-- 12 = face, clock that has to close

def Clock := Fin 720

-- 12-face: 12 marks = 60° each. Checking the face is O(1)
def check12 (c : Clock) : Bool :=
  c.val % 60 == 0

-- 3-divisible: balanced pair. 60 % 3 = 0, so 12-face is always balanced
def isBalanced (c : Clock) : Bool :=
  c.val % 3 == 0

-- 6-bank: distance to next balanced mark (how far you have to crank to build)
def buildDist (c : Clock) : Nat :=
  if isBalanced c then 0 else (3 - c.val % 3) % 3

-- Theorem 1: 60 divisible by 3, so 12-face check closes balanced check
theorem check12_implies_balanced (c : Clock) :
  check12 c = true → isBalanced c = true := by
  intro h
  simp [check12, isBalanced] at *
  have : c.val % 60 = 0 := h
  have h60 : 60 % 3 = 0 := by rfl
  -- if val % 60 = 0 then val % 3 = 0 because 3 | 60
  omega

-- Theorem 2: balanced check means bounded build - you never crank more than 2°
theorem balanced_implies_bounded_build (c : Clock) :
  buildDist c ≤ 2 := by
  unfold buildDist isBalanced
  split
  · omega
  · have : c.val % 3 < 3 := Nat.mod_lt _ (by omega)
    omega

-- The receipt: 720 % 3 = 0, so the 12-face always closes the 720 crank within 2°
-- This is your 1-3-6-9-12: 1 event, 3 pair, 6 bank, 9 overlap, 12 face
theorem check_closes_build_of_div3 :
  720 % 3 = 0 ∧ ∀ c : Clock, check12 c = true → buildDist c = 0 := by
  constructor
  · rfl
  · intro c h
    have hb := check12_implies_balanced c h
    simp [buildDist, hb]
