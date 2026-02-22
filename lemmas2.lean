import Relativity.lemmas
import Relativity.definitions
noncomputable section

open scoped RealInnerProductSpace
open EuclideanSpace
set_option relaxedAutoImplicit true
-- Harmonic `generalize_proofs` tactic

noncomputable def slopeVec (v : R2) : ℝ := v 1 / v 0

lemma slopeVec_mul_eq_neg_one_of_perp
  {v w : R2} (hvx : v 0 ≠ 0) (hwx : w 0 ≠ 0) (hperp : ⟪v, w⟫ = 0) : slopeVec v * slopeVec w = -1 := by
    classical
    have hsum' : ∑ i : Fin 2, v i * w i = 0 := by
      rw [PiLp.inner_apply v w] at hperp
      simp
      simp at hperp
      rw [mul_comm] at hperp
      rw [mul_comm (w 1) (v 1)] at hperp
      exact hperp
    have hsum : v 0 * w 0 + v 1 * w 1 = 0 := by
      simpa [Fin.sum_univ_two] using hsum'
    have hv1w1 : v 1 * w 1 = -(v 0 * w 0) :=
      eq_neg_of_add_eq_zero_right hsum
    have hden_ne : v 0 * w 0 ≠ 0 := mul_ne_zero hvx hwx
    calc
      slopeVec v * slopeVec w
          = (v 1 / v 0) * (w 1 / w 0) := rfl
      _ = (v 1 * w 1) / (v 0 * w 0) := by
        ring
      _ = (-(v 0 * w 0)) / (v 0 * w 0) := by simp [hv1w1]
      _ = -((v 0 * w 0) / (v 0 * w 0)) := by simp [neg_div]
      _ = -1 := by simp [hden_ne]

lemma lightLikeEq : ∀ (x y : R4), lightLike x y → x 3 = y 3 → x = y := by
  intro x y hllxy hx3eqy3
  unfold lightLike at hllxy
  have htdzero : timeDistanceSq x y = 0 := by
    unfold timeDistanceSq
    rw [hx3eqy3]
    simp
  have hsdzero : spaceDistanceSq x y = 0 := by
    rw [htdzero] at hllxy
    assumption
  exact sp_tm_eq_eq x y hsdzero hx3eqy3

lemma lightLikeSpanEq : ∀ (x z w: R4), lightLike x z → lightLike w x → lightLike w z →
  (x 3 = w 3 ∨ z 3 = w 3) → w ∈ affineSpan ℝ {x, z} := by
    intro x z w hllxz hllwx hllwz hteq
    obtain h1|h2 := hteq
    have := lightLikeEq x w (lightLikeSymm w x hllwx) h1
    rw [this]
    have : w ∈ ({w,z} : Set R4) := by simp
    exact mem_affineSpan ℝ this
    have := lightLikeEq z w (lightLikeSymm w z hllwz) h2
    rw [this]
    have : w ∈ ({x,w} : Set R4) := by simp
    exact mem_affineSpan ℝ this

lemma sqrtTimeDistance : ∀ (x y : R4), √ (timeDistanceSq x y) = abs (x 3 - y 3) := by
  intro x y
  unfold timeDistanceSq
  simpa using (Real.sqrt_sq_eq_abs (x 3 - y 3))

lemma sqrtSpaceDistance : ∀ (x y : R4), √ (spaceDistanceSq x y) = dist (spatial x) (spatial y) := by sorry







lemma lightLikeSpanLt : ∀ (x z w: R4), lightLike x z → lightLike w x → lightLike w z →
  (x 3 < z 3 ∧ z 3 < w 3) ∨ (x 3 < w 3 ∧ w 3 < z 3) ∨ (w 3 < x 3 ∧ x 3 < z 3) →
  w ∈ affineSpan ℝ {x, z} := by sorry

theorem tangentPlaneToCone : ∀ (x y : R4), spaceDistanceSq x y > timeDistanceSq x y →
  ∃ (z : R4), x ≠ z ∧ lightLike x z ∧ ∀ (s t : R4), affineSpan ℝ ({s,t} : Set R4) ≤  affineSpan ℝ ({x, y, z} : Set R4) → lightLike s t → (affineSpan ℝ ({s,t} : Set R4)).Parallel  (affineSpan ℝ ({x,z} : Set R4)) := sorry

theorem lightLikeSpan' : ∀ (x z w: R4), lightLike x z → lightLike w x → lightLike w z → x ≠ z →
  w ∈ affineSpan ℝ {x, z} := by
    intro x z w hllxz hllwx hllwz hxnez
    by_cases hxz : x 3 ≤ z 3
    by_cases hzw : z 3 ≤ w 3
    apply le_iff_eq_or_lt.mp at hxz
    apply le_iff_eq_or_lt.mp at hzw
    obtain h1|h2 := hxz
    have := lightLikeEq x z hllxz h1
    contradiction
    obtain h3|h4 := hzw
    exact lightLikeSpanEq x z w hllxz hllwx hllwz (Or.inr h3)
    exact lightLikeSpanLt x z w hllxz hllwx hllwz (Or.inl (And.intro h2 h4))
    apply le_iff_eq_or_lt.mp at hxz
    obtain h1|h2 := hxz
    have := lightLikeEq x z hllxz h1
    contradiction
    apply not_le.mp at hzw
    by_cases hxw : x 3 ≤ w 3
    apply le_iff_eq_or_lt.mp at hxw
    obtain h1|h2 := hxw
    exact lightLikeSpanEq x z w hllxz hllwx hllwz (Or.inl h1)
    exact lightLikeSpanLt x z w hllxz hllwx hllwz (Or.inr (Or.inl (And.intro h2 hzw)))
    apply not_le.mp at hxw
    exact lightLikeSpanLt x z w hllxz hllwx hllwz (Or.inr (Or.inr (And.intro hxw h2)))
    apply not_le.mp at hxz
    by_cases hwx : w 3 ≤ x 3
    apply le_iff_eq_or_lt.mp at hwx
    obtain h1|h2 := hwx
    exact lightLikeSpanEq x z w hllxz hllwx hllwz (Or.inl h1.symm)
    by_cases hzw : z 3 ≤ w 3
    apply le_iff_eq_or_lt.mp at hzw
    obtain h1|h3 := hzw
    exact lightLikeSpanEq x z w hllxz hllwx hllwz (Or.inr h1)
    have := lightLikeSpanLt z x w (lightLikeSymm x z hllxz) hllwz hllwx (Or.inr (Or.inl (And.intro h3 h2)))
    simpa [Set.pair_comm] using this
    apply not_le.mp at hzw
    have := lightLikeSpanLt z x w (lightLikeSymm x z hllxz) hllwz hllwx (Or.inr (Or.inr (And.intro hzw hxz)))
    simpa [Set.pair_comm] using this
    apply not_le.mp at hwx
    have := lightLikeSpanLt z x w (lightLikeSymm x z hllxz) hllwz hllwx (Or.inl (And.intro hxz hwx))
    simpa [Set.pair_comm] using this

theorem zExist : ∀ (x y : R4), spaceDistanceSq x y > timeDistanceSq x y → ∃ (z : R4),
  lightLike x z ∧ ∀ (w : R4), ¬ (lightLike w x ∧ lightLike w y ∧ lightLike w z) := by
    intro x y hsdgttd
    have := tangentPlaneToCone x y hsdgttd
    obtain ⟨z, ⟨hxnez, hllxz, hparallel⟩⟩  := this
    use z
    constructor
    exact hllxz
    by_contra hw
    push_neg at hw
    obtain ⟨w,⟨hllwx, hllwy, hllwz⟩ ⟩ := hw
    have hwxyz := hparallel w y
    have hwInxzSpan: w ∈ affineSpan ℝ {x,z} := lightLikeSpan' x z w hllxz hllwx hllwz hxnez
    have haffineSub: affineSpan ℝ {w, y} ≤ affineSpan ℝ {x, y, z} := by
      have : {w,y}  ⊆ ((affineSpan ℝ {x, y, z}) : Set R4) := by
        simp only [Set.insert_subset_iff]
        constructor
        have hle :
            affineSpan ℝ ({x, z} : Set R4) ≤
              affineSpan ℝ ({x, y, z} : Set R4) := by
          apply affineSpan_mono
          intro t ht
          have hxz : t = x ∨ t = z := by
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
          rcases hxz with rfl | rfl
          · simp [Set.mem_insert_iff, Set.mem_singleton_iff]
          · simp [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact hle hwInxzSpan
        have hy_mem : y ∈ (affineSpan ℝ {x, y, z}) := by
          have : y ∈ ({x,y,z} : Set R4) := by simp
          apply mem_affineSpan ℝ this
        simpa [Set.singleton_subset_iff] using hy_mem
      exact affineSpan_le.mpr this
    have hAffineParallel := hwxyz haffineSub hllwy
    apply AffineSubspace.Parallel.direction_eq at hAffineParallel
    have hn : ((affineSpan ℝ {w, y} : Set R4) ∩ (affineSpan ℝ {x, z} : Set R4)).Nonempty := by
      use w
      constructor
      have : w ∈ ({w,y} : Set R4) := by simp
      have := mem_spanPoints ℝ w {w,y} this
      assumption
      assumption
    have hAffinesEqual := AffineSubspace.ext_of_direction_eq hAffineParallel hn
    have : affineSpan ℝ {w, y} = affineSpan ℝ {x, z} → spanPoints ℝ {w,y} = spanPoints ℝ {x,z} := by
      intro h
      have h' := congrArg (fun S : AffineSubspace ℝ R4 => (S : Set R4)) h
      simpa [coe_affineSpan] using h'
    apply this at hAffinesEqual
    have hSetsEqual : (affineSpan ℝ {w, y} : Set R4) = (affineSpan ℝ {x,z} : Set R4) := by
      rw [coe_affineSpan]
      rw [coe_affineSpan]
      rw [hAffinesEqual]
    have : y ∈ ({w,y} : Set R4) := by simp
    have hyInwy := mem_spanPoints ℝ y {w,y} this
    have : y ∈ (affineSpan ℝ {x,z} : Set R4) := by
      rw[coe_affineSpan]
      rw [← hAffinesEqual]
      assumption
    have hynInxz : y ∉ spanPoints ℝ ({x,z}: Set R4) := by
      intro hyInSpanxz
      have hllxy := lightLikeSpan x y z hllxz hyInSpanxz
      unfold lightLike at hllxy
      rw [hllxy] at hsdgttd
      linarith
    contradiction

theorem wExist : ∀ (x y z : R4),
  spatial x = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] →
  spatial y = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] →
  lightLike x z →
  ∃ (w : R4), lightLike w x ∧ lightLike w y ∧ lightLike w z := by sorry

/-
noncomputable def T_of_vw
    (v w : R4) (a b c d : ℝ)
    (b4 : Module.Basis (Fin 4) ℝ R4)
    (hv : b4 0 = v) (hw : b4 1 = w) : R4 →ₗ[ℝ] R2 :=
  b4.constr ℝ ![![a, b], ![c, d], 0, 0]

@[simp] lemma T_of_vw_on_v
    (v w : R4) (a b c d : ℝ)
    (b4 : Module.Basis (Fin 4) ℝ R4)
    (hv : b4 0 = v) (hw : b4 1 = w) :
    T_of_vw v w a b c d b4 hv hw v = ![a, b] := by
  classical
  have := (b4.constr_basis ℝ ![![a, b], ![c, d], 0, 0] 0)
  simpa [T_of_vw, hv]

@[simp] lemma T_of_vw_on_w
    (v w : R4) (a b c d : ℝ)
    (b4 : Module.Basis (Fin 4) ℝ R4)
    (hv : b4 0 = v) (hw : b4 1 = w) :
    T_of_vw v w a b c d b4 hv hw w = ![c, d] := by
  classical
  have := (b4.constr_basis ℝ ![![a, b], ![c, d], 0, 0] 1)
  simpa [T_of_vw, hw]


theorem orthoProjection : ∀ (x y z : R4), spatial x = ![0,0,0] → spatial y = ![0,0,0] →
  let dir := affineSpan ℝ ({x, z} : Set R4);
  let w := EuclideanGeometry.orthogonalProjection dir (y - x);
  (timeDistanceSq y w) * (spaceDistanceSq x w) = (timeDistanceSq x w) * (spaceDistanceSq y w) := by sorry
-/
