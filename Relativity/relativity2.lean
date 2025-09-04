import Relativity.lemmas
open scoped RealInnerProductSpace
open EuclideanSpace

theorem norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ x

theorem norm_sq_is_sum_of_squares : ∀ (v : R3), (v 0)^2 + (v 1)^2 + (v 2)^2 = (norm v) ^ 2 := by
  intro v
  rw [norm_sq_eq]
  norm_num
  have hcoords :
      (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = ∑ x : Fin 3, (v x) ^ 2 := by
    simpa using
      (Fin.sum_univ_three (fun x : Fin 3 => (v x) ^ 2)).symm
  exact hcoords

theorem spaceNormSqConstant : ∀ (c : ℝ) (v : R3), spaceNormSq (c • v) = (c ^ 2) * (norm v) ^ 2 := by
  intro c v
  unfold spaceNormSq
  simp
  rw [mul_pow, mul_pow, mul_pow]
  rw [← mul_add, ← mul_add]
  field_simp
  left
  exact norm_sq_is_sum_of_squares v

theorem spatialDiff : ∀ (x y : R4), spatial x - spatial y = ![x 0 - y 0, x 1 - y 1, x 2 - y 2] := by
  intro x y
  unfold spatial
  aesop

theorem zExistsxtneyt : ∀ (x y : R4), spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 → x 3 ≠ y 3 →
  ∃ (z : R4), spaceDistanceSq z x = abs ( z 3 - x 3) ^ 2
  ∧ (z 3 - x 3) ≠ 0
  ∧ z 3 = y 3
  ∧ ⟪ spatial z - spatial x, spatial z - spatial y ⟫ = 0 := by
    intro x y hxyspaceLike xtneyt
    let yxSpatialDiff : R3 := ![y 0 - x 0, y 1 - x 1, y 2 - x 2]
    let ws : R3 := (norm yxSpatialDiff) ^ (-1 : ℝ )  • yxSpatialDiff
    let wsPerp : R3 := √((y 2 - x 2) ^ 2 + (x 1 - y 1) ^ 2)  • ![y 2 - x 2, x 1 - y 1, 0]
    let zs := (((abs (y 3 - x 3)) ^ 2 / norm yxSpatialDiff) • ws) + wsPerp
    let z := ![zs 0, zs 1, zs 2, y 3]
    sorry

theorem zExistsxteqyt : ∀ (x y : R4), spaceDistanceSq x y > (x 3 - y 3) ^ 2 → x 3 = y 3 →
            ∃ (z : R4), spaceDistanceSq z x = ( z 3 - x 3) ^ 2
            ∧ z 3 - x 3 ≠ 0
            ∧ ⟪ spatial z - spatial x, spatial y - spatial x ⟫ = 0 := by
  intro x y hxyspaceLike xteqyt
  let yxSpatialDiff : R3 := ![y 0 - x 0, y 1 - x 1, y 2 - x 2]
  let ws : R3 := (norm yxSpatialDiff) ⁻¹  • yxSpatialDiff
  let wsPerp : R3 := ((√((y 2 - x 2) ^ 2 + (x 1 - y 1) ^ 2))⁻¹)  • ![y 2 - x 2, x 1 - y 1, 0]
  let zs1 : R3 := ((norm yxSpatialDiff) • wsPerp)
  let zt : ℝ := (norm yxSpatialDiff) + x 3
  let z : R4 := ![zs1 0 + x 0, zs1 1 + x 1, zs1 2 + x 2, zt]

  use z
  constructor
  case h.left := by sorry
    /- have h0 : z 3 - x 3 = norm yxSpatialDiff := by
      simp [z,zt]
    rw [h0]
    have hzsub : spatial z - spatial x = (norm yxSpatialDiff) • wsPerp := by
      unfold spatial
      ext i
      aesop
    have hwsPerpNorm : norm wsPerp = 1 := by
      simp only [wsPerp]
      rw [norm_smul _ _]
      rw [norm_eq]
      norm_num
      simp
      have hsum : ∑ i : Fin 3, (![y 2 - x 2, x 1 - y 1, 0] i) ^ 2 = (y 2 - x 2) ^ 2 + (x 1 - y 1) ^ 2 := by sorry
      rw [hsum]
      have  : 0 ≤ √((y 2 - x 2) ^ 2 + (x 1 - y 1) ^ 2)  := Real.sqrt_nonneg _
      rw [abs_of_nonneg this]
      rw [mul_comm]
      #check Field.mul_inv_cancel



    unfold spaceDistanceSq
    rw [hzsub]
    rw [spaceNormSqConstant (norm yxSpatialDiff) wsPerp]
    rw [hwsPerpNorm]
    simp

  case h.right := by
    constructor
    case left =>
      intro h0
      simp [z, zt] at h0
      rw [xteqyt] at hxyspaceLike
      simp at hxyspaceLike
      simp [yxSpatialDiff] at h0
      rw [spaceDistComm x y] at hxyspaceLike
      unfold spaceDistanceSq at hxyspaceLike
      rw [spatialDiff y x, h0] at hxyspaceLike
      unfold spaceNormSq at hxyspaceLike
      simp at hxyspaceLike-/
  case h.right := by sorry


theorem x_ne_y_imp_x'_ne_y' : ∀ (x y x' y': R4), x ≠ y →
  ∀ (m k : B), IOb m → IOb k → events m x = events k x' → events m y = events k y' → x' ≠ y' := by
    intro x y x' y' hxney m k iom _ hxx'EventsEq hyy'EventsEq hx'eqy'
    rw [← hx'eqy'] at hyy'EventsEq
    rw [← hyy'EventsEq] at hxx'EventsEq
    have hxx'EventsNotEq := x_ne_y_evx_ne_evy x y m iom hxney
    exact hxx'EventsNotEq hxx'EventsEq

theorem lightLikeImplightLike: ∀ (x y x' y' : R4), ∀ (m k : B), IOb m → IOb k →
  lightLike x y → events m x = events k x' -> events m y = events k y' → lightLike x' y' := by
    intro x y x' y' m k iom iok hllxy hxx'EventsEq hyy'EventsEq
    unfold lightLike at *
    obtain ⟨p, hp, hwmpx, hwmpy⟩ := (axph m x y iom).mpr hllxy
    have hwkpx' : W k p x' := by
      have hpInEvmx := (eventsToWorldview p m x).mpr hwmpx
      rw [hxx'EventsEq] at hpInEvmx
      exact (eventsToWorldview p k x').mp hpInEvmx
    have hwkpy' : W k p y' := by
      have hpInEvmy := (eventsToWorldview p m y).mpr hwmpy
      rw [hyy'EventsEq] at hpInEvmy
      exact (eventsToWorldview p k y').mp hpInEvmy
    exact (axph k x' y' iok).mp ⟨p, ⟨hp, hwkpx', hwkpy'⟩⟩

theorem zExist : ∀ (x y : R4), spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 → ∃ (z : R4),
  lightLike x z ∧ x ≠ z ∧ y ≠ z ∧
  ∀ (w : R4), ¬ (lightLike w x ∧ lightLike w y ∧ lightLike w z) := sorry


#check dist_add_dist_eq_iff
#check AffineSubspace.affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty

theorem notFasterThanLight : ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ x ≠ y ∧ IOb m ∧ IOb k →
  ¬ spaceDistanceSq x y > abs (x 3 - y 3) ^ 2 := by
    intro m k x y ⟨hwmkx, hwmky, xney, iom, iok⟩ spaceDistGreater
    have zwExist := zExist x y spaceDistGreater
    obtain ⟨z, ⟨hxzLightlike, ⟨xnez, ynez, hwNotExist⟩⟩⟩  := zwExist
    obtain ⟨x', hx'⟩ := axev m k iom iok x
    obtain ⟨y', hy'⟩ := axev m k iom iok y
    obtain ⟨z', hz'⟩ := axev m k iom iok z
    have x'sZero : spatial x' = ![0,0,0] := by
      have wkkx' : W k k x' := by
        apply (eventsToWorldview k k x').mp
        rw [← hx']
        apply (eventsToWorldview k m x).mpr
        assumption
      have hx's000 := axsf k iok x' wkkx'
      simp [hx's000]
      unfold spatial
      ext i
      aesop
    have y'sZero : spatial y' = ![0,0,0] := by
      have wkky' : W k k y' := by
        apply (eventsToWorldview k k y').mp
        rw [← hy']
        apply (eventsToWorldview k m y).mpr
        assumption
      have hy's000 := axsf k iok y' wkky'
      simp [hy's000]
      unfold spatial
      ext i
      aesop
    have x'ney' : x' ≠ y' := x_ne_y_imp_x'_ne_y' x y x' y' xney m k iom iok hx' hy'
    have x'nez' : x' ≠ z' := x_ne_y_imp_x'_ne_y' x z x' z' xnez m k iom iok hx' hz'
    have y'nez' : y' ≠ z' := x_ne_y_imp_x'_ne_y' y z y' z' ynez m k iom iok hy' hz'
    have hx'z'Lightlike : lightLike x' z' := lightLikeImplightLike x z x' z' m k iom iok hxzLightlike hx' hz'
    have ⟨w', ⟨hllw'x', hllw'y', hllw'z'⟩⟩ : ∃ (w' : R4),
      lightLike w' x' ∧
      lightLike w' y' ∧
      lightLike w' z' := by sorry


    obtain ⟨w, hwEvents⟩  := axev k m iok iom w'
    have hw : lightLike w x ∧ lightLike w y ∧ lightLike w z := by
      constructor
      case left := lightLikeImplightLike w' x' w x k m iok iom hllw'x' hwEvents hx'.symm
      case right := by
        constructor
        case left := lightLikeImplightLike w' y' w y k m iok iom hllw'y' hwEvents hy'.symm
        case right := lightLikeImplightLike w' z' w z k m iok iom hllw'z' hwEvents hz'.symm
    have hwNot := hwNotExist w
    contradiction
