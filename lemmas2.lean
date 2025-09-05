import Relativity.definitions

theorem eventsToWorldview : ∀ (b ob : B), ∀ (x : R4), b ∈ events ob x ↔ W ob b x := by
  intro b ob x
  rw [events]
  simp

theorem spaceDistComm : ∀ (x y: R4), spaceDistanceSq x y = spaceDistanceSq y x := by
  intro x y
  unfold spaceDistanceSq
  unfold spatial
  unfold spaceNormSq
  simp
  ring

theorem x_ne_y_evx_ne_evy : ∀ (x y : R4) (b : B), IOb b → x ≠ y → events b x ≠ events b y := by sorry
