-- /One/ThreeMachine.lean - 1-3-6-9-12 maps chassis
def Clock := Fin 720
def onFace (c : Clock) : Bool := c.val % 60 == 0
def balanced (c : Clock) : Bool := c.val % 3 == 0
theorem face_balanced (c : Clock) : onFace c = true -> balanced c = true := by simp [onFace, balanced] at *; omega
theorem closes : 720 % 3 = 0 := rfl
