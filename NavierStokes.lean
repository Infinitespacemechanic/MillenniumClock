-- /Four/NavierStokes.lean - 1-3-6-9-12 keeps it smooth
def Clock := Fin 720
def onFace (c : Clock) : Bool := c.val % 60 == 0
def smooth (c : Clock) : Bool := c.val % 3 == 0
theorem face_smooth (c : Clock) : onFace c = true -> smooth c = true := by simp [onFace, smooth] at *; omega
theorem closes : 720 % 3 = 0 := rfl
