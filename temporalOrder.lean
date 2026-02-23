import Relativity.lemmas
import Relativity.lemmas2
import Relativity.definitions
noncomputable section

set_option relaxedAutoImplicit true
-- Harmonic `generalize_proofs` tactic

variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

-- Theorem: "In special relativity, different inertial observers may disagree on the temporal order of events"
theorem temporalOrderParadox : SpecRel B IB Ph W → ∀ (m k : B) (v : ℝ),
  IOb B IB W m ∧ IOb B IB W k ∧ velocitySq B W m k v ∧ v > 0 →
  ∃ (b1 b2: B) (t1 t2 t3 t4: ℝ), timeOfEvent B W m b1 t1 ∧ timeOfEvent B W m b2 t2 ∧
  timeOfEvent B W k b1 t3 ∧ timeOfEvent B W k b2 t4 ∧ t1 < t2 ∧ t4 < t3 := by sorry
