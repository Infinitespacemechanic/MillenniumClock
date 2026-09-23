-- /Five/YangMillsGap.lean - 1-3-6-9-12 has weight
-- Yang-Mills mass gap in diesel hours: does the balancer have mass?

-- 1 = gauge event - one field stroke, one power stroke
-- 3 = pair, balanced pair needs weight to spin
-- 6 = bank, six phased gauge fields around 720
-- 9 = overlap, 3x3 guarantees no massless dead spot
-- 12 = face - balancer face, does it have weight or spin free?

def Clock := Fin 720

-- Balancer face = 12 marks = 60° each. Balanced check O(1)
def onBalancerFace (c : Clock) : Bool :=
  c.val % 60 == 0

-- Balanced gauge - divisible by 3, harmonic stays with weight
def isBalancedGauge (c : Clock) : Bool :=
  c.val % 3 == 0

-- F = M R ω² - mass needed to hold rotation
-- If balanced, needs at least 1 unit mass to keep spinning
-- If off face, mass leaks as heat (Bottle 3 leak)
def massHeld (c : Clock) : Nat :=
  if isBalancedGauge c then 1 else 0

-- Mass gap - how far off massless (0 = massless, 1 = has gap)
def massGap (c : Clock) : Nat :=
  if isBalancedGauge c then 1 else 0

-- Unbalanced leak - how much energy flies if off 3-pair
def leakDist (c : Clock) : Nat :=
  if isBalancedGauge c then 0 else (3 - c.val % 3) % 3

-- Theorem 1: balancer face is always balanced because 60 % 3 = 0
-- Balanced face must have weight to spin - can't be massless
theorem balancerFace_is_balanced (c : Clock) :
  onBalancerFace c = true → isBalancedGauge c = true := by
  intro h
  simp [onBalancerFace, isBalancedGauge] at *
  have : c.val % 60 = 0 := h
  omega

-- Theorem 2: mass gap bounded below by 1 when balanced - minimum weight
-- No massless gauge on the balancer face
theorem mass_gap_bounded_below (c : Clock) :
  isBalancedGauge c = true → massGap c ≥ 1 := by
  intro h
  simp [massGap, h]

-- Theorem 3: leak bounded to ≤2° if you bookkeep in 3's
-- Unbalanced field can't fly far - at most 2° leak
theorem leak_bounded (c : Clock) :
  leakDist c ≤ 2 := by
  unfold leakDist isBalancedGauge
  split
  · omega
  · have : c.val % 3 < 3 := Nat.mod_lt _ (by omega)
    omega

-- The receipt: 720 % 3 = 0, so 12-face balancer must have mass gap
-- If gauge ticks in 3's, balancer can't spin massless - needs ≥1
theorem gap_closes_of_div3 :
  720 % 3 = 0 ∧ ∀ c : Clock, onBalancerFace c = true → massGap c = 1 ∧ massHeld c = 1 := by
  constructor
  · rfl
  · intro c h
    have hb := balancerFace_is_balanced c h
    simp [massGap, massHeld, hb]

-- Interpretation: Yang-Mills mass gap = does balancer have weight?
-- In this model: yes, if you bookkeep in 3's, balanced gauge must have mass
-- Off face = unbalanced = massless leak = F = M R ω² flies off, heat
-- On face = balanced = has gap = needs weight to keep 720 spinning, standing wave holds
