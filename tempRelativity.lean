import Relativity.relativity
noncomputable section
set_option relaxedAutoImplicit true

variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

-- "m sees eventBody at location x"
def locOfEvent (m : B) (eventBody : B) (x : R4) : Prop := W m eventBody x

-- "m sees the time between events as t"
def timeBetweenEvents (m eventBody1 eventBody2 : B) (t : ℝ) : Prop :=
  ∃ (x1 x2 : R4), W m eventBody1 x1 ∧ W m eventBody2 x2 ∧ timeDistanceSq x1 x2 = t * t

-- "m sees the spatial distance between events as s"
def spaceBetweenEvents (m eventBody1 eventBody2 : B) (s : ℝ) : Prop :=
  ∃ (x1 x2 : R4), W m eventBody1 x1 ∧ W m eventBody2 x2 ∧ spaceDistanceSq x1 x2 = s * s

-- the Minkowski metric between two points in R4
def minkowskiMetricSqPoints (p q : R4) : ℝ := timeDistanceSq p q - spaceDistanceSq p q

-- "m sees the Minkowski metric between events as r"
def minkowskiMetricSqEvents (m : B) (eventBody1 eventBody2 : B) (r : ℝ) : Prop :=
  ∃ (x1 x2 : R4), W m eventBody1 x1 ∧ W m eventBody2 x2 ∧ minkowskiMetricSqPoints x1 x2 = r * r

-- "all inertial observers see the same Minkowski metric between events"
theorem minkowskiMetricInvariant B IB Ph W : SpecRel B IB Ph W →
  ∀ (m k : B) (eventBody1 eventBody2 : B) (r : ℝ),
  IOb B IB W m ∧ IOb B IB W k → ((minkowskiMetricSqEvents B W m eventBody1 eventBody2 r) ↔
                                (minkowskiMetricSqEvents B W k eventBody1 eventBody2 r)) := by
    contrapose!;
    simp +zetaDelta at *;
    intro m k hm hk eventBody1 eventBody2 r h;
    intro h1 h2 h3;
    use m, hm, m, hm;
    use 0; norm_num [ events ];
    refine' ⟨ EuclideanSpace.single 0 1, _, 0, 0, _, _, _ ⟩ <;> norm_num [ spaceDistanceSq ];
    · decide +revert;
    · unfold spaceNormSq; norm_num [ spatial ] ;
      norm_num [ Fin.ext_iff ]
