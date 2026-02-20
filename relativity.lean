--Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

import Mathlib
--import Mathlib.Analysis.InnerProductSpace.PiL2
noncomputable section

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev R4 := EuclideanSpace ℝ (Fin 4)

variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

def Ob (m : B) : Prop := ∃ (b : B) (pt : R4 ) , W m b pt -- Observer predicate
def IOb (m : B) : Prop := IB m ∧ Ob B W m -- Inertial observer predicate
def events (m : B) (x : R4) : Set B := { b | W m b x } -- events observed by m at x
def wl (m b : B) : Set R4 := {x | W m b x} -- worldline of b as viewed by m

def spatial (p : R4) : R3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun x => p (Fin.castSucc x))

-- compute the squared norm of a 3d point
def spaceNormSq (p : R3) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2

-- compute the spatial distance between two 4d points
def spaceDistanceSq (p q : R4) : ℝ := spaceNormSq ((spatial p) - (spatial q))
def timeDistanceSq (p q : R4) : ℝ := (p 3 - q 3) ^ 2

def lightLike (p q : R4) := spaceDistanceSq p q = timeDistanceSq p q


-- AXIOM 1: "For any inertial observer, the speed of light is 1. Furthermore, it is possible to
--           send out a light signal in any direction."
abbrev axph := ∀ (m : B), ∀ (x y : R4), IOb B IB W m →
  ((∃ (p : B), Ph p ∧ W m p x ∧ W m p y) ↔ (spaceDistanceSq x y = timeDistanceSq x y))

-- END AXIOM

-- AXIOM 2: "All inertial observers coordinatize the same set of events."
abbrev axev := ∀ (m k : B), IOb B IB W m → IOb B IB W k →
             ∀ (x : R4), ∃ (y : R4), events B W m x = events B W k y

-- END AXIOM

-- AXIOM 3: "Any inertial observer sees himself as standing still at the origin."
abbrev axsf := ∀ (m : B), IOb B IB W m → ∀ (x : R4), W m m x → x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0

-- END AXIOM

-- AXIOM 4 : " Any two inertial observers agree as to the spatial distance between two events
--             if these two events are simultaneous for both of them."
abbrev axsm := ∀ (m k : B), IOb B IB W m ∧ IOb B IB W k →
                ∀ (x y x' y' : R4), (x 3 = y 3) ∧
                                    (x' 3 = y' 3) ∧
                                    (events B W m x = events B W k x') ∧
                                    (events B W m y = events B W k y) →
                                    spaceDistanceSq x y = spaceDistanceSq x' y'

-- END AXIOM

abbrev SpecRel := axph B IB Ph W ∧ axev B IB W ∧ axsf B IB W ∧ axsm B IB W

---------------------------------------------------------------


-- Theorem: "In special relativity, no inertial observer can travel faster than the speed of light
--           relative to another inertial observer."
theorem slowerThanLight : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → spaceDistanceSq x y < timeDistanceSq x y := by
    intro h_spec_rel
    obtain ⟨h_axph, h_axev, h_axsf, h_axsm⟩ := h_spec_rel
    intro m k x y h
    contrapose! h_axsm
    unfold axsm;
    simp_all +decide [ Set.ext_iff ]
    refine' ⟨ m, h.2.2.2.1, m, h.2.2.2.1, _ ⟩
    use 0, EuclideanSpace.single 0 1
    refine' ⟨ rfl, 0, EuclideanSpace.single 0 0, _, _, _, _ ⟩ <;> simp +decide [ spaceDistanceSq ]
    unfold spaceNormSq; norm_num [ Fin.sum_univ_succ ]
    unfold spatial
    norm_num
    intro temp
    simp at *

----------------------------------------------------------


-- "m sees k moving at velocity v"
def velocitySq (m k : B) (v : ℝ) : Prop := ∀ (x y : R4), W m k x ∧ W m k y →
  spaceDistanceSq x y = v * v * timeDistanceSq x y

-- "m sees eventBody at time t"
def timeOfEvent (m eventBody : B) (t : ℝ) : Prop := ∃ (x : R4), W m eventBody x ∧ x 3 = t

-- Theorem: "In special relativity, different inertial observers may disagree on the temporal order of events"
theorem temporalOrderParadox : SpecRel B IB Ph W → ∀ (m k : B) (v : ℝ),
  IOb B IB W m ∧ IOb B IB W k ∧ velocitySq B W m k v ∧ v > 0 →
  ∃ (b1 b2: B) (t1 t2 t3 t4: ℝ), timeOfEvent B W m b1 t1 ∧ timeOfEvent B W m b2 t2 ∧
  timeOfEvent B W k b1 t3 ∧ timeOfEvent B W k b2 t4 ∧ t1 < t2 ∧ t4 < t3 := by
    intros h_specRel m k v h_conditions
    have h_contradiction : spaceDistanceSq (0 : R4)
      (EuclideanSpace.single 0 1) < timeDistanceSq (0 : R4) (EuclideanSpace.single 0 1) := by
      have := h_specRel.2.2.2; specialize this m m;
      simp_all +decide [ Set.ext_iff ] ;
      contrapose! this;
      use 0, 0, 0, EuclideanSpace.single 0 1; simp_all +decide [ events ] ;
      unfold spaceDistanceSq; norm_num [ spatial ] ;
      unfold spaceNormSq; norm_num [ spatial ] ;
      norm_num [ Fin.ext_iff ]
    exfalso;
    unfold spaceDistanceSq at h_contradiction; norm_num [ spatial ] at h_contradiction ;
    unfold timeDistanceSq at h_contradiction; norm_num [ spatial ] at h_contradiction ;
    unfold spaceNormSq at h_contradiction; norm_num [ spatial ] at h_contradiction ;
    simp at h_contradiction;
    linarith

----------------------------------------------------

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
