import Relativity.relativity
noncomputable section
set_option relaxedAutoImplicit true

variable (B : Type) -- Bodies
variable (IB : B → Prop) -- Inertial bodies predicate
variable (Ph : B → Prop) -- Photon predicate
variable (W : B → B → R4 → Prop) -- Worldview predicate

def velocitySq (m k : B) (v : ℝ) : Prop := ∀ (x y : R4), W m k x ∧ W m k y →
  spaceDistanceSq x y = v * v * timeDistanceSq x y

def time (m eventBody : B) (t : ℝ) : Prop := ∃ (x : R4), W m eventBody x ∧ x 3 = t

theorem temporalOrderParadox : SpecRel B IB Ph W → ∀ (m k : B) (v : ℝ),
  IOb B IB W m ∧ IOb B IB W k ∧ velocitySq B W m k v ∧ v > 0 →
  ∃ (b1 b2: B) (t1 t2 t3 t4: ℝ), time B W m b1 t1 ∧ time B W m b2 t2 ∧
  time B W k b1 t3 ∧ time B W k b2 t4 ∧ t1 < t2 ∧ t4 < t3 := by
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
