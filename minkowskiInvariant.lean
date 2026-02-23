--import Relativity.lemmas
--import Relativity.lemmas2
import Relativity.definitions
noncomputable section

set_option relaxedAutoImplicit true
-- Harmonic `generalize_proofs` tactic

variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

-- "all inertial observers see the same Minkowski metric between events"
theorem minkowskiMetricInvariant B IB Ph W : SpecRel B IB Ph W →
  ∀ (m k : B) (eventBody1 eventBody2 : B) (r : ℝ),
  IOb B IB W m ∧ IOb B IB W k → ((minkowskiMetricSqEvents B W m eventBody1 eventBody2 r) ↔
                                (minkowskiMetricSqEvents B W k eventBody1 eventBody2 r)) := by sorry
