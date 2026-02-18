import Harmonic.lemmas
set_option relaxedAutoImplicit true
-- Harmonic `generalize_proofs` tactic

variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

theorem notLightSpeed : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → ¬ spaceDistanceSq x y = timeDistanceSq x y := by sorry

/-
theorem notFasterThanLight : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → ¬ spaceDistanceSq x y = timeDistanceSq x y := by sorry
-/
