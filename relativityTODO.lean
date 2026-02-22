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

-- Theorem: "In special relativity, different inertial observers may disagree on the temporal order of events"
theorem temporalOrderParadox : SpecRel B IB Ph W → ∀ (m k : B) (v : ℝ),
  IOb B IB W m ∧ IOb B IB W k ∧ velocitySq B W m k v ∧ v > 0 →
  ∃ (b1 b2: B) (t1 t2 t3 t4: ℝ), timeOfEvent B W m b1 t1 ∧ timeOfEvent B W m b2 t2 ∧
  timeOfEvent B W k b1 t3 ∧ timeOfEvent B W k b2 t4 ∧ t1 < t2 ∧ t4 < t3 := by sorry

  -- "all inertial observers see the same Minkowski metric between events"
theorem minkowskiMetricInvariant B IB Ph W : SpecRel B IB Ph W →
  ∀ (m k : B) (eventBody1 eventBody2 : B) (r : ℝ),
  IOb B IB W m ∧ IOb B IB W k → ((minkowskiMetricSqEvents B W m eventBody1 eventBody2 r) ↔
                                (minkowskiMetricSqEvents B W k eventBody1 eventBody2 r)) := by sorry
