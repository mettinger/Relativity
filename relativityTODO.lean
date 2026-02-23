import Relativity.lemmas
import Relativity.definitions
noncomputable section
set_option relaxedAutoImplicit true

variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

-- Theorem: "In special relativity, no inertial observer can travel faster than the speed of light
--           relative to another inertial observer."
theorem slowerThanLight : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → spaceDistanceSq x y < timeDistanceSq x y := by sorry
