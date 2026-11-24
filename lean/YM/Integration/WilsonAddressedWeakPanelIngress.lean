import YM.Integration.WilsonAddressedWeakStampedCourse
import YM.Integration.WilsonAddressedWeakReflectedHearing
import YM.Integration.WilsonAddressedWeakFiledTargets
import YM.Integration.WilsonAddressedWeakEnrollment

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakPanelIngress
open Function Set Filter MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue Marker Push.Corrected
open Next.Rank Next.Rank.Edition Next.Rank.Station Next.Rank.Peak Next.Rank.Tapes Next.Rank.Atlas
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedHearing WilsonThermometerReflectedTrajectory
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {k N p j:ℕ} (live:k≤N)
local notation "Lev" => R.family.path.levels
theorem push {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c:Course R.family N p k) (A:Config G (R.family.side N p)→E) (hj:j≤N) (hk:k≤j):
    c.flow A j hj=gust R.family.path N p N A j hj:=by
  induction hj using Nat.decreasingInduction with
  | self=>rw [c.flow_self,gust_base]
  | of_succ i hi ih=>
    rw [c.flow_step _ i hi,gust_step _ _ _ _ _ hi,c.same _ (hk.trans (Nat.le_succ i)) hi,
      ih (hk.trans (Nat.le_succ i))]

theorem stamped (b:ℝ) (d:Fin 2→ℕ) (z:Fin 2→Site (R.family.side N p))
    (y:(i:Fin 2)→Palette R.family (d i)) (r:(i:Fin 2)→Emblems R.family (d i)):
    let χ:=width (Lev) b k
    let gr:χ≤k:=(wider ..).trans (before ..)
    let T:=Ship.yard R.family b live p
    let F:=WilsonThermometerIntrinsicRoster.source R d z y r live
    Array.stamp T (R.family.beta N p) (Read.bareP F)=
      Accent.birth (Stock.census (T.Cell × Fin 2)) (R.family.path.rep N p N)
        (WilsonAddressedWeakCopiedProducts.field R gr live d z y r):=by
  intro χ gr T F
  ext1 U
  ext a
  apply Eq.trans _ (WilsonAddressedWeakCopiedProducts.original R gr live d z y r a U).symm
  rw [Array.stamp_part,Marks.divides]
  congr 1

theorem density (b:ℝ) (d:Fin 2→ℕ) (z:Fin 2→Site (R.family.side N p))
    (y:(i:Fin 2)→Palette R.family (d i)) (r:(i:Fin 2)→Emblems R.family (d i)) (hk:k<N)
    (c:Course R.family N p k) (hj:j≤N) (lower:k≤j):
    let χ:=width (Lev) b k
    let gr:χ≤k:=(wider ..).trans (before ..)
    let T:=Ship.yard R.family b live p
    let F:=WilsonThermometerIntrinsicRoster.source R d z y r live
    c.flow (Array.stamp T (R.family.beta N p) (Read.bareP F)) j hj=
      WilsonThermometerReflectedRoster.density R (fun i:T.Cell×Fin 2=>d i.2) (fun i=>z i.2)
        (motion R gr hk) (anchor R gr) (fun i=>y i.2) (fun i=>r i.2) (Stock.census (T.Cell×Fin 2)) live hj:=by
  intro χ gr T F
  rw [stamped R live b d z y r,push R c _ hj lower]
  rfl

private theorem same {n : Side} (A : Ratio n n) (x : Site n) : A.embed x=x := by
  have count : A.count.val=1 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0<n.val from n.property); simpa only [Nat.mul_one] using A.exact_size.symm
  rw [Ratio.embed,count,one_smul,wrap_lift]

theorem seats_original (b:ℝ) (x:Points 2) (hk:k<N):
    let χ:=width (Lev) b k
    let gr:χ≤k:=(wider ..).trans (before ..)
    let ρ:=gap (Lev) b k
    let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
    let v:=projected R (p:=p) live ρ (gap_pos ..) x
    origins R gr hk z=seats R.family b v live p:=by
  intro χ gr ρ z v
  funext i
  have h:=WilsonThermometerReflectedRoster.parent R (z i.2) (motion R gr hk i) (anchor R gr i) le_rfl live
  change WilsonThermometerOwnOffsetNectar.location R _ k=_
  rw [h]
  change affine _ (anchorAt R _ k) (WilsonThermometerOwnOffsetNectar.location R (z i.2) k)=_
  rw [show seats R.family b v live p i=_ from fills R.family v b p live le_rfl gr i,homeHere]
  have ht:Station.choose (Lev) b k v=lifts R (p:=p) live ρ (gap_pos ..) x:=
    (WilsonAddressedWeakMaxwellPositions.stations R (p:=p) live b x).2.1
  rw [ht,←(actual R (p:=p) live ρ (gap_pos ..) x).1 i.2]
  simp only [anchorAt,Mix.camp,dif_pos (le_refl k),same,
    WilsonThermometerOwnOffsetNectar.location,dif_pos live]
  rfl
end YM.Integration.WilsonAddressedWeakPanelIngress
end
