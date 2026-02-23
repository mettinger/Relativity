import Relativity.lemmas
import Relativity.definitions
noncomputable section

open scoped RealInnerProductSpace
open EuclideanSpace
set_option relaxedAutoImplicit true
set_option maxHeartbeats 1000000
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

lemma sqrtSpaceDistance : ∀ (x y : R4), √ (spaceDistanceSq x y) = dist (spatial x) (spatial y) := by
  have h_dist : ∀ (v w : R3), dist v w = Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2)) := by
    intros v w
    simp [dist_eq_norm, EuclideanSpace.norm_eq];
    rw [ Fin.sum_univ_three ] ; ring;
  intros x y
  rw [h_dist];
  unfold spaceDistanceSq; ring;
  exact congrArg Real.sqrt ( by unfold spaceNormSq; norm_num [ spatial ] ; ring )

lemma lightLikeSpanLt : ∀ (x z w: R4), lightLike x z → lightLike w x → lightLike w z →
  (x 3 < z 3 ∧ z 3 < w 3) ∨ (x 3 < w 3 ∧ w 3 < z 3) ∨ (w 3 < x 3 ∧ x 3 < z 3) →
  w ∈ affineSpan ℝ {x, z} := by
    intros x z w hxz hxw hwz h_order
    have h_affine : w ∈ affineSpan ℝ {x, z} := by
      have h_affine : ∃ (a b : ℝ), a + b = 1 ∧ w = a • x + b • z := by
        obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, w 3 = a * x 3 + b * z 3 ∧ a + b = 1 := by
          use (w 3 - z 3) / (x 3 - z 3), 1 - (w 3 - z 3) / (x 3 - z 3);
          grind;
        have h_affine : (w 0 - a * x 0 - b * z 0)^2 + (w 1 - a * x 1 - b * z 1)^2 + (w 2 - a * x 2 - b * z 2)^2 = 0 := by
          unfold lightLike at *;
          unfold spaceDistanceSq timeDistanceSq at *;
          unfold spaceNormSq at *; norm_num [ spatial ] at *;
          grind;
        exact ⟨ a, b, hab.2, by ext i; fin_cases i <;> norm_num <;> nlinarith! only [ h_affine, hab ] ⟩;
      rcases h_affine with ⟨ a, b, hab, rfl ⟩ ; rw [ affineSpan ] ; simp +decide [ hab ] ;
      simp +decide [ spanPoints ];
      -- Since $a + b = 1$, we can rewrite $a • x + b • z$ as $a • (x - z) + z$.
      have h_rewrite : a • x + b • z = a • (x - z) + z := by
        rw [ show b = 1 - a by linarith ] ; ext ; norm_num ; ring;
      simp +decide [ h_rewrite, vectorSpan_pair ];
      exact Or.inr ⟨ a • ( x - z ), Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_singleton _ ) ), rfl ⟩
    exact h_affine


noncomputable section AristotleLemmas

/-
Definition of Minkowski inner product and its relation to lightlike vectors.
-/
def minkowskiInner (x y : R4) : ℝ := x 3 * y 3 - ⟪spatial x, spatial y⟫

lemma lightLike_iff_minkowski_zero (x : R4) : lightLike 0 x ↔ minkowskiInner x x = 0 := by
  unfold lightLike minkowskiInner;
  unfold spaceDistanceSq timeDistanceSq;
  unfold spaceNormSq;
  unfold spatial; norm_num [ Fin.sum_univ_three, Inner.inner ] ; ring;
  constructor <;> intro h <;> linarith!

/-
Characterization of spacelike vectors using the Minkowski inner product.
-/
lemma spacelike_iff_minkowski_neg (x : R4) : spaceDistanceSq 0 x > timeDistanceSq 0 x ↔ minkowskiInner x x < 0 := by
  unfold spaceDistanceSq timeDistanceSq minkowskiInner;
  unfold spaceNormSq;
  unfold spatial;
  norm_num [ Fin.sum_univ_three, inner ] ; ring

/-
Symmetry of the Minkowski inner product.
-/
lemma minkowskiInner_symm (x y : R4) : minkowskiInner x y = minkowskiInner y x := by
  unfold minkowskiInner;
  norm_num [ mul_comm, inner_sum, inner_smul_left, inner_smul_right ];
  rw [ real_inner_comm ]

/-
Bilinearity of the Minkowski inner product.
-/
lemma minkowskiInner_bilin (a b : ℝ) (x y z : R4) : minkowskiInner (a • x + b • y) z = a * minkowskiInner x z + b * minkowskiInner y z := by
  unfold minkowskiInner;
  unfold spatial; norm_num [ Fin.sum_univ_three, Inner.inner ] ; ring;

/-
For any non-zero vector v in R3, there exists a non-zero vector w orthogonal to v.
-/
lemma exists_orth_nonzero_of_nonzero (v : R3) (hv : v ≠ 0) : ∃ w : R3, w ≠ 0 ∧ ⟪v, w⟫ = 0 := by
  by_contra! h_contra;
  have h_lin_dep : ∀ x : Fin 3 → ℝ, x ≠ 0 → ⟪v, x⟫ ≠ 0 := by
    exact?;
  contrapose! h_lin_dep;
  by_cases hv0 : v 0 = 0;
  · exact ⟨ fun i => if i = 0 then 1 else 0, by intros h; simpa using congr_fun h 0, by simp +decide [ hv0, inner ] ⟩;
  · use ![ -v 1, v 0, 0 ];
    simp_all +decide [ Fin.sum_univ_three, inner ];
    ring

/-
For any vector s in R3 and scalar a such that a^2 < |s|^2, there exists a unit vector w such that w . s = a.
-/
lemma exists_unit_vec_dot_eq (s : R3) (a : ℝ) (h : a^2 < spaceNormSq s) : ∃ w : R3, spaceNormSq w = 1 ∧ ⟪w, s⟫ = a := by
  -- By `exists_orth_nonzero_of_nonzero`, there exists a non-zero vector n orthogonal to s.
  obtain ⟨n, hn_ne_zero, hn_orth⟩ : ∃ n : R3, n ≠ 0 ∧ ⟪s, n⟫ = 0 := by
    convert exists_orth_nonzero_of_nonzero s _ using 1;
    exact fun h' => by simp_all +decide [ spaceNormSq ] ; nlinarith;
  -- Normalize n to get a unit vector u orthogonal to s.
  obtain ⟨u, hu_unit, hu_orth⟩ : ∃ u : R3, spaceNormSq u = 1 ∧ ⟪s, u⟫ = 0 := by
    use (1 / Real.sqrt (spaceNormSq n)) • n;
    unfold spaceNormSq at *; simp_all +decide [ inner_smul_left, inner_smul_right ] ;
    field_simp;
    rw [ Real.sq_sqrt <| by positivity, div_self <| by intro H; exact hn_ne_zero <| by ext i; fin_cases i <;> norm_num <;> nlinarith! ];
  -- We seek w of the form c * s + d * u.
  obtain ⟨c, d, hc, hd⟩ : ∃ c d : ℝ, c * spaceNormSq s = a ∧ c^2 * spaceNormSq s + d^2 = 1 := by
    use a / spaceNormSq s, Real.sqrt (1 - (a / spaceNormSq s)^2 * spaceNormSq s);
    rw [ Real.sq_sqrt ] <;> norm_num [ show spaceNormSq s ≠ 0 by nlinarith ];
    rw [ div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ show 0 < spaceNormSq s from lt_of_le_of_lt ( sq_nonneg a ) h ];
  refine' ⟨ c • s + d • u, _, _ ⟩ <;> simp_all +decide [ spaceNormSq, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right ];
  · simp_all +decide [ Fin.sum_univ_three, inner ];
    linear_combination' hd + hu_unit * d ^ 2 + hu_orth * 2 * c * d;
  · simp_all +decide [ EuclideanSpace.norm_eq, Fin.sum_univ_three, inner_self_eq_norm_sq_to_K ];
    rw [ Real.sq_sqrt ( by positivity ), inner_eq_zero_symm.mp hu_orth ] ; linarith

/-
For any spacelike vector v, there exists a non-zero lightlike vector u orthogonal to v.
-/
lemma exists_null_orth_spacelike (v : R4) (hv : minkowskiInner v v < 0) : ∃ u, u ≠ 0 ∧ minkowskiInner u u = 0 ∧ minkowskiInner u v = 0 := by
  obtain ⟨s, t, hs⟩ : ∃ s : R3, ∃ t : ℝ, v = ![s 0, s 1, s 2, t] := by
    use ![v 0, v 1, v 2], v 3;
    ext i; fin_cases i <;> rfl;
  -- By `exists_unit_vec_dot_eq`, there exists a unit vector $w \in \mathbb{R}^3$ such that $w \cdot s = t$.
  obtain ⟨w, hw⟩ : ∃ w : R3, spaceNormSq w = 1 ∧ ⟪w, s⟫ = t := by
    apply exists_unit_vec_dot_eq;
    unfold minkowskiInner at hv; simp_all +decide [ spaceNormSq ] ;
    convert hv using 1 ; ring! ; norm_num [ Fin.sum_univ_three, inner ] ; ring!;
  refine' ⟨ fun i => if i = 0 then w 0 else if i = 1 then w 1 else if i = 2 then w 2 else 1, _, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_three ];
  · exact fun h => by simpa using congr_fun h 3;
  · unfold minkowskiInner;
    unfold spatial; simp +decide [ Fin.sum_univ_three ] ;
    simp_all +decide [ Fin.sum_univ_three, spaceNormSq ];
    simp_all +decide [ Fin.sum_univ_three, inner ];
    linarith;
  · unfold minkowskiInner; simp +decide [ Fin.sum_univ_three ] ;
    unfold spatial; simp +decide [ Fin.sum_univ_three ] ; linarith!;

/-
If u is lightlike, v is spacelike, and u is orthogonal to v, then any lightlike vector w in the plane spanned by u and v must be a scalar multiple of u.
-/
lemma null_vector_in_plane_of_null_and_spacelike_orth (u v w : R4)
  (hu : minkowskiInner u u = 0)
  (hv : minkowskiInner v v < 0)
  (huv : minkowskiInner u v = 0)
  (hw : w ∈ Submodule.span ℝ {u, v})
  (hw_null : minkowskiInner w w = 0) :
  ∃ k : ℝ, w = k • u := by
    -- Since w is in the span of u and v, we can write w = a • u + b • v for some scalars a and b.
    obtain ⟨a, b, hw_eq⟩ : ∃ a b : ℝ, w = a • u + b • v := by
      rw [ Submodule.mem_span_pair ] at hw ; tauto;
    -- Then minkowskiInner w w = a^2 * (u . u) + 2ab * (u . v) + b^2 * (v . v).
    have h_inner : minkowskiInner w w = a^2 * minkowskiInner u u + 2 * a * b * minkowskiInner u v + b^2 * minkowskiInner v v := by
      unfold minkowskiInner at *;
      simp +decide [ hw_eq, spatial ];
      norm_num [ Fin.sum_univ_three, inner ] ; ring;
    aesop

end AristotleLemmas

theorem tangentPlaneToCone : SpecRel B IB Ph W → ∀ (x y : R4),
  spaceDistanceSq x y > timeDistanceSq x y →
  ∃ (z : R4), x ≠ z ∧
  lightLike x z ∧
  ∀ (s t : R4), s ≠ t → affineSpan ℝ ({s,t} : Set R4) ≤  affineSpan ℝ ({x, y, z} : Set R4) →
    lightLike s t → (affineSpan ℝ ({s,t} : Set R4)).Parallel  (affineSpan ℝ ({x,z} : Set R4)) := by
      intro h x y;
      intro hxy
      obtain ⟨u, hu_ne_zero, hu_lightlike, hu_orthogonal⟩ : ∃ u : R4, u ≠ 0 ∧ minkowskiInner u u = 0 ∧ minkowskiInner u (y - x) = 0 := by
        apply exists_null_orth_spacelike;
        unfold minkowskiInner; simp [timeDistanceSq, spaceDistanceSq] at *; (
        convert hxy using 1 <;> norm_num [ spaceNormSq ] ; ring;
        unfold spatial; norm_num [ Fin.sum_univ_three, inner ] ; ring;);
      refine' ⟨ x + u, _, _, _ ⟩ <;> simp_all +decide [ lightLike ];
      · unfold minkowskiInner at *;
        unfold spaceDistanceSq timeDistanceSq; simp_all +decide [ EuclideanSpace.norm_eq ] ;
        simp_all +decide [ spatial, spaceNormSq, inner ];
        norm_num [ Fin.sum_univ_three ] at * ; linarith!;
      · intro s t hst h_affine h_lightlike
        obtain ⟨w, hw⟩ : ∃ w : R4, w ≠ 0 ∧ w ∈ Submodule.span ℝ {u, y - x} ∧ minkowskiInner w w = 0 ∧ w = t - s := by
          have h_w_in_span : t - s ∈ Submodule.span ℝ {u, y - x} := by
            have h_w_in_span : t - s ∈ (affineSpan ℝ {x, y, x + u}).direction := by
              exact AffineSubspace.vsub_mem_direction ( h_affine <| mem_affineSpan ℝ <| Set.mem_insert_of_mem _ <| Set.mem_singleton _ ) ( h_affine <| mem_affineSpan ℝ <| Set.mem_insert _ _ );
            rw [ direction_affineSpan ] at h_w_in_span;
            rw [ vectorSpan_eq_span_vsub_set_right ] at h_w_in_span;
            case p => exact x;
            · simp_all +decide [ Submodule.mem_span ];
              intro p hp; specialize h_w_in_span p; simp_all +decide [ Set.insert_subset_iff, Set.singleton_subset_iff ] ;
            · norm_num;
          refine' ⟨ t - s, sub_ne_zero.mpr ( Ne.symm hst ), h_w_in_span, _, rfl ⟩;
          convert sub_eq_zero.mpr h_lightlike using 1;
          unfold minkowskiInner spaceDistanceSq timeDistanceSq; norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] ; ring;
          unfold spaceNormSq; norm_num [ Fin.sum_univ_three, inner_sub_left, inner_sub_right ] ; ring;
          unfold spatial; norm_num [ Fin.sum_univ_three, inner ] ; ring;
          unfold spaceDistanceSq timeDistanceSq at h_lightlike; norm_num [ Fin.sum_univ_three, spaceNormSq ] at h_lightlike; linarith!;
        -- By `null_vector_in_plane_of_null_and_spacelike_orth`, $w = k • u$ for some $k$.
        obtain ⟨k, hk⟩ : ∃ k : ℝ, w = k • u := by
          apply null_vector_in_plane_of_null_and_spacelike_orth;
          any_goals tauto;
          unfold timeDistanceSq spaceDistanceSq minkowskiInner at *;
          unfold spaceNormSq at *;
          unfold spatial at *;
          norm_num [ Fin.sum_univ_three, inner ] at * ; linarith!;
        refine' ⟨ _, _ ⟩;
        exact -s + x;
        refine' le_antisymm _ _;
        · rw [ affineSpan_le ];
          intro p hp; rcases hp with ( rfl | rfl ) <;> simp +decide [ *, Set.insert_subset_iff ] ;
          · exact ⟨ s, subset_spanPoints ℝ _ <| Set.mem_insert _ _, by abel1 ⟩;
          · refine' ⟨ s + ( 1 / k ) • ( t - s ), _, _ ⟩ <;> simp_all +decide [ spanPoints ];
            · refine' Or.inl ⟨ k⁻¹ • ( t - s ), _, _ ⟩ <;> simp_all +decide [ vectorSpan_pair ];
              · rw [ Submodule.mem_span_singleton ];
                exact ⟨ -k⁻¹, by ext; simp +decide [ sub_eq_add_neg ] ; ring ⟩;
              · abel1;
            · simp +decide [ ← hw.2.2.2, hw.1, smul_smul ] ; abel_nf;
        · rw [ AffineSubspace.map_le_iff_le_comap ];
          rw [ affineSpan_le ];
          simp_all +decide [ Set.insert_subset_iff, AffineSubspace.mem_comap ];
          simp_all +decide [ spanPoints ];
          simp_all +decide [ vectorSpan_pair ];
          simp_all +decide [ Submodule.mem_span_singleton ];
          exact Or.inl ⟨ -k, by ext i; have := congr_fun hw.2.2.2 i; norm_num at *; linarith ⟩

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

theorem zExist : SpecRel B IB Ph W → ∀ (x y : R4), spaceDistanceSq x y > timeDistanceSq x y → ∃ (z : R4),
  lightLike x z ∧ ∀ (w : R4), ¬ (lightLike w x ∧ lightLike w y ∧ lightLike w z) := by
    intro specRel x y hsdgttd

    have := tangentPlaneToCone specRel x y hsdgttd
    obtain ⟨z, ⟨hxnez, hllxz, hparallel⟩⟩  := this
    use z
    constructor
    exact hllxz
    by_contra hw
    push_neg at hw
    obtain ⟨w,⟨hllwx, hllwy, hllwz⟩ ⟩ := hw

    by_cases hweqy : w = y
    rw [hweqy] at hllwx
    unfold lightLike at hllwx
    rw [← timeDistanceComm x y] at hllwx
    rw [← hllwx] at hsdgttd
    rw [spaceDistanceComm x y] at hsdgttd
    linarith only [hsdgttd]
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
    have hAffineParallel := hwxyz hweqy haffineSub hllwy
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


/-
Defines a helper function `mk_w` to construct a 4-vector from a spatial vector and a time component, and a lemma stating that its spatial component is the original vector.
-/
open scoped RealInnerProductSpace
open EuclideanSpace

def mk_w (v : R3) (t : ℝ) : R4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm ![v 0, v 1, v 2, t]

@[simp]
lemma spatial_mk_w (v : R3) (t : ℝ) : spatial (mk_w v t) = v := by
  ext i; fin_cases i <;> rfl;

/-
Lemma stating that the time component of `mk_w v t` is `t`.
-/
@[simp]
lemma time_mk_w (v : R3) (t : ℝ) : (mk_w v t) 3 = t := by
  exact?

/-
Defines the witness point `w` for the theorem `wExist`.
It sets the time component to the midpoint of `x` and `y`'s times.
For the spatial component, it distinguishes two cases based on whether `x` and `z` are simultaneous.
-/
def w_witness (x y z : R4) : R4 :=
  let t := (x 3 + y 3) / 2
  if h : x 3 = z 3 then
    mk_w ((WithLp.equiv 2 (Fin 3 → ℝ)).symm ![t - x 3, 0, 0]) t
  else
    let scale := (x 3 - t) / (x 3 - z 3)
    mk_w (scale • spatial z) t

/-
Lemma stating that the witness point `w` constructed by `w_witness` is light-like separated from `x`, `y`, and `z`, under the given conditions.
-/
lemma w_witness_works (x y z : R4)
  (hx : spatial x = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0])
  (hy : spatial y = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0])
  (hl : lightLike x z) :
  lightLike (w_witness x y z) x ∧ lightLike (w_witness x y z) y ∧ lightLike (w_witness x y z) z := by
    unfold lightLike at *;
    unfold w_witness; simp_all +decide [ spaceDistanceSq, timeDistanceSq ] ;
    split_ifs <;> simp_all +decide [ spaceNormSq, spatial ];
    · unfold mk_w; simp +decide [ hx, hy, hl ] ; ring;
      norm_num [ show z 0 = 0 by nlinarith, show z 1 = 0 by nlinarith, show z 2 = 0 by nlinarith ];
    · unfold mk_w; simp +decide [ *, Fin.sum_univ_three ] ; ring;
      grind

theorem wExist : ∀ (x y z : R4),
  spatial x = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] →
  spatial y = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] →
  lightLike x z →
  ∃ (w : R4), lightLike w x ∧ lightLike w y ∧ lightLike w z := by
    intros x y z hx hy hl;
    have := w_witness_works x y z hx hy hl;
    exact ⟨ _, this ⟩



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
