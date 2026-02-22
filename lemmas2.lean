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

theorem tangentPlaneToCone : SpecRel B IB Ph W → ∀ (x y : R4),
  spaceDistanceSq x y > timeDistanceSq x y →
  ∃ (z : R4), x ≠ z ∧
  lightLike x z ∧
  ∀ (s t : R4), affineSpan ℝ ({s,t} : Set R4) ≤  affineSpan ℝ ({x, y, z} : Set R4) →
    lightLike s t → (affineSpan ℝ ({s,t} : Set R4)).Parallel  (affineSpan ℝ ({x,z} : Set R4)) := by sorry

/-
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

noncomputable section AristotleLemmas

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

end AristotleLemmas

theorem wExist : ∀ (x y z : R4),
  spatial x = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] →
  spatial y = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0,0,0] →
  lightLike x z →
  ∃ (w : R4), lightLike w x ∧ lightLike w y ∧ lightLike w z := by
    intros x y z hx hy hl;
    have := w_witness_works x y z hx hy hl;
    exact ⟨ _, this ⟩

-/




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
