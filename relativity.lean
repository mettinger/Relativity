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

theorem slowerThanLight : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → spaceDistanceSq x y < timeDistanceSq x y := by
    intro h_spec_rel
    obtain ⟨h_axph, h_axev, h_axsf, h_axsm⟩ := h_spec_rel;
    intro m k x y h;
    contrapose! h_axsm;
    unfold axsm; simp_all +decide [ Set.ext_iff ] ;
    refine' ⟨ m, h.2.2.2.1, m, h.2.2.2.1, _ ⟩;
    -- Let's choose x to be the origin and x_1 to be a point with a non-zero spatial component but the same time component as x.

    use 0, EuclideanSpace.single 0 1;
    refine' ⟨ rfl, 0, EuclideanSpace.single 0 0, _, _, _, _ ⟩ <;> simp +decide [ spaceDistanceSq ];
    unfold spaceNormSq; norm_num [ Fin.sum_univ_succ ] ;
    unfold spatial; norm_num;
    intro temp
    simp at *

/-
theorem notLightSpeed : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → ¬ spaceDistanceSq x y = timeDistanceSq x y := by
    contrapose!;
    rintro ⟨ m, k, x, y, h, h' ⟩;
    intro h''; have := h''.right.right.right; simp_all +decide [ SpecRel, axsm ] ;
    contrapose! this;
    use m, m;
    refine' ⟨ h.2.2.2.1, h.2.2.2.1, _ ⟩;
    use 0, EuclideanSpace.single 0 1, 0, 0 ; norm_num [ events ];
    unfold spaceDistanceSq; norm_num;
    unfold spaceNormSq; norm_num [ spatial ] ;
    norm_num [ Fin.ext_iff ]


theorem notFasterThanLight : SpecRel B IB Ph W → ∀ (m k : B), ∀ (x y : R4),
  W m k x ∧
  W m k y ∧
  x ≠ y ∧
  IOb B IB W m ∧
  IOb B IB W k → ¬ spaceDistanceSq x y > timeDistanceSq x y := by
    intro h_specRel m k x y h_event
    by_contra h_contra
    have h_observer : ∃ m : B, IOb B IB W m ∧ (spaceDistanceSq x y > timeDistanceSq x y) := by
      exact ⟨ m, h_event.2.2.2.1, h_contra ⟩;
    have := h_specRel.2.2.2;
    have := this m m; simp_all +decide [ Set.ext_iff ] ;
    contrapose! this;
    use 0, 0, 0, EuclideanSpace.single 0 1; simp_all +decide [ events ] ;
    unfold spaceDistanceSq; norm_num;
    unfold spaceNormSq; norm_num [ spatial ] ;
    norm_num [ Fin.ext_iff ]
-/
