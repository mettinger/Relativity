import Relativity.lemmas2
open scoped RealInnerProductSpace
open EuclideanSpace


theorem zExist : ∀ (x y : R4), spaceDistanceSq x y > timeDistanceSq x y → ∃ (z : R4),
  lightLike x z ∧ ∀ (w : R4), ¬ (lightLike w x ∧ lightLike w y ∧ lightLike w z) := by
    intro x y hsdgttd
    by_cases ht : x 3 = y 3
    case pos := sorry
    case neg := sorry

#check dist_add_dist_eq_iff
#check AffineSubspace.affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty

theorem wExist : ∀ (x y z : R4), spatial x = ![0,0,0] → spatial y = ![0,0,0]
  → lightLike x z → ∃ (w : R4), lightLike w x ∧ lightLike w y ∧ lightLike w z := by
    intro x y z xsZero ysZero lightLikexz

    let dir := affineSpan ℝ ({x, z} : Set R4)
    let w := EuclideanGeometry.orthogonalProjection dir (y - x)
    have hwInDir := EuclideanGeometry.orthogonalProjection_mem (s := dir) (p := y - x)
    use w
    constructor
    case h.left := (lightLikeSymm x w) (lightLikeSpan x w z lightLikexz hwInDir)
    constructor
    case h.right.right := by
      have : ({x, z} : Set R4) = ({z, x} : Set R4) := by apply Set.pair_comm
      have : affineSpan ℝ ({x, z} : Set R4) = affineSpan ℝ ({z, x} : Set R4) := by
        rw [← this]
      have : ↑w ∈ affineSpan ℝ {z, x} := by
        conv =>
          congr
          rw [← this]
          rfl
        apply hwInDir
      exact (lightLikeSymm z w) (lightLikeSpan z w x ((lightLikeSymm x z) lightLikexz) this)
    case h.right.left := by
      unfold lightLike




theorem notFasterThanLight : ∀ (m k : B), ∀ (x y : R4), W m k x ∧ W m k y ∧ IOb m ∧ IOb k →
  ¬ spaceDistanceSq x y > timeDistanceSq x y := by
    intro m k x y ⟨hwmkx, hwmky, iom, iok⟩ spaceDistGreater
    have zwExist := zExist x y spaceDistGreater
    obtain ⟨z, ⟨hxzLightlike, hwNotExist⟩⟩  := zwExist
    --obtain ⟨z, ⟨hxzLightlike, ⟨hnColxyz, hwNotExist⟩⟩⟩  := zwExist
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
      unfold spatial
      ext i
      aesop

    have hx'z'Lightlike : lightLike x' z' := lightLikeImplightLike x z x' z' m k iom iok hxzLightlike hx' hz'

    have ⟨w', ⟨hllw'x', hllw'y', hllw'z'⟩⟩ : ∃ (w' : R4),
      lightLike w' x' ∧
      lightLike w' y' ∧
      lightLike w' z' := wExist x' y' z' x'sZero y'sZero hx'z'Lightlike
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
