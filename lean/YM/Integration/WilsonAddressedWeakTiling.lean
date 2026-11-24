import YM.Integration.WilsonAddressedWeakReflectedArray
import YM.Integration.WilsonAddressedWeakChamber

/-! The original centered chessboard gives compatible signed copies of the same two numerical fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakTiling

open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open Cells MergeProof Accent Motion PhysicalNext.Repeat.Legato
open WilsonThermometerReflectedTrajectory
open scoped Classical

variable {G : Gauge} (R : Run G)

private theorem composed {n m l : Side} (A : Ratio n m) (B : Ratio m l) (C : Ratio n l)
    (x : Site n) : B.embed (A.embed x) = C.embed x := by
  have counts : A.count.val*B.count.val=C.count.val := by
    apply Nat.eq_of_mul_eq_mul_left (show 0<n.val from n.property)
    rw [← Nat.mul_assoc,← A.exact_size,← B.exact_size,← C.exact_size]
  have hl : lift (B.embed (A.embed x)) = lift (C.embed x) := by
    rw [B.lift_embed,A.lift_embed,C.lift_embed,smul_smul,Nat.mul_comm,counts]
  simpa only [wrap_lift] using congrArg (wrap l) hl

private theorem same {n : Side} (A : Ratio n n) (x : Site n) : A.embed x=x := by
  have count : A.count.val=1 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0<n.val from n.property); simpa only [Nat.mul_one] using A.exact_size.symm
  rw [Ratio.embed,count,one_smul,wrap_lift]

/-- At the reporting date the physical anchors of different reflection cells have the full native period spacing. -/
theorem spacing {u k p : ℕ} (hk:u≤k) (x y:Site (R.family.side u p)) (hxy:x ≠ y) :
    (R.family.S.toDepth hk p).count.val ≤
    separation (anchorAt R ((R.family.S.toDepth hk p).embed x) k)
      (anchorAt R ((R.family.S.toDepth hk p).embed y) k) := by
  let g := R.family.S.toDepth hk p
  simp only [anchorAt,Mix.camp,dif_pos (le_refl k),same]
  change g.count.val ≤ pdist (g.embed x-g.embed y)
  rw [← g.root_embed,← g.root_embed,← map_sub,g.root_embed]
  have hx : ∃ i, lift (x-y) i≠0 := by
    by_contra! hl
    apply hxy; apply sub_eq_zero.mp
    rw [← wrap_lift (x-y),show lift (x-y)=0 from funext hl]; exact map_zero _
  obtain ⟨i,hi⟩ := hx
  refine le_trans ?_ (component_le (g.embed (x-y)) i)
  rw [g.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hi)

/-- The translation in each original reflected copy equals the actual upper-date embedding of its reporting anchor. -/
theorem translation {u k N p : ℕ} (hk:u≤k) (hN:k≤N) (j : Site (R.family.side u p)) :
    let T := Cells.center R.family.S p (hk.trans hN) 0
    T.translateBy j=anchorAt R ((R.family.S.toDepth hk p).embed j) N := by
  dsimp only; rw [anchorAt,Mix.camp,dif_pos hN,composed _ _ (R.family.S.toDepth (hk.trans hN) p)]
  have h := Cells.copy_home R.family.S (hk.trans hN) (0 : Site (R.family.side N p)) j
  simpa [Tiling.copyMap,affine,Signed.act] using h

/-- Every true phase and conjugation of a fully enrolled scalar field is the one used by the actual tiling. -/
theorem physical {u k N p : ℕ} (hk:u≤k) (hN:k≤N) (j : Site (R.family.side u p))
    (F : Config G (R.family.side N p) → ℂ) (U : Config G (R.family.side N p)) :
    let T := Cells.center R.family.S p (hk.trans hN) 0
    T.copy j F U = stepUp (T.omega j,T.hand j)
      (anchorAt R ((R.family.S.toDepth hk p).embed j) N) F U := by
  dsimp only; rw [← translation R hk hN j]; simp only [Tiling.copy,stepUp,Motion.scalar,decide_eq_true_eq]

end YM.Integration.WilsonAddressedWeakTiling
