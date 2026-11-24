import YM.Integration.WilsonPhysicalAllGradeWeakElection
import YM.Integration.WilsonPhysicalWeakSameStation
import YM.Integration.WilsonPhysicalHousedOpticalSchool
import YM.Integration.WilsonOriginalTwoFlatIRPoolBook
import YM.Integration.WilsonOlderFreshSoftSocketStationPooledRestored

/-! All seven pooled thermal readings on the original Born-oriented station and its two physical stops. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalObservedRoseBornBook
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedMixedMasterSchool (field)
open WilsonMeasuredPublicEntrancePanelSchool (Registered)
open WilsonPhysicalWeakWallBounded
open WilsonPhysicalWeakWallBooks
open WilsonPhysicalWeakWallSequence
open WilsonPhysicalWeakWallStaff
open WilsonPhysicalWeakWallSequence
open Next.UVStress
open scoped Classical Topology BigOperators
open WilsonPositionThermometerGradedSource (grade)
open OPE Overlay FVA2 Next.Rank Marker MergeProof Accent
open Extraction Table Spec Wilson Source Labels Extra.Histories
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Extra.Trajectories Push.GridApprox.Nil
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress
open Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent RG16 RG16.Literal
variable {G:Gauge}{R:Run G}{simple:G.Simple}

theorem original {axis:Axis}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}{campaign:Campaign R}
    {W:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (WilsonOriginalOpticalSchedule.prepared s) R campaign W)
    {v:Extraction.Order}{S:Table R.family.book}(F:Final R.family v S){l:Ultrafilter (ℕ×ℕ)}
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}(J:ℝ→PhysMS.tower S)
    (bliss:Bliss F l z H)(lead:Leading F J)(axes:∀g,∀ᶠr in trail,Frame.obedient F H (J r) g)
    (birth:WilsonPhysicalAllGradeWeakElection.Assignment F J H l simple)
    (Z:WilsonPrescription G){n:ℕ}(positive:0<n)(ratio:Z.run.ratio=(3:ℕ)^n)(stage:ℕ)
    (color:G.ColorIndex)(paths:FundedOriginalVacuumPaths.prices R.kit):
    ∃t ≥ 6+3,∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(r:{r:ℝ // 0<r ∧ r<δ})→Book F (l:=l) H z 6 T r.val,
    (∀r,∃live:6≤(birth.day r.val).1,WilsonPhysicalWeakWallBooks.Shared F (books r)
      (WilsonPhysicalWeakSameStation.trim live (birth.day r.val).2)) ∧
    ∃priced:∀r,WilsonMovingForkWindowBooks.Priced F (books r),
    (∀(h:ℕ)(d:Fin 3→Fin 7)(y:∀i,(Spin.comparator R.family.book).Field (d i).val)
      (x:∀i,RG17.Free R.family (d i).val),
      ∃grant:Registered F 6 T h t d books (field F J Z 6 T d y x books),type_of%
        (WilsonIndependentMeasuredOpticalSchool.original F Z simple bliss
          (WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid).2.1 (axis:=axis) (ε:=Stroke.epsilonR)
          paid.nested.2 positive ratio stage grant)) ∧
    (∀{a u:ℕ},Stop R.family 0 a u → Facilities R.family v S → (l:Filter _)≤v.fuse →
      ∀(h:ℕ)(x:∀i:Fin 3,RG17.Free R.family (grade i).val)(φ:Test 3),
        WilsonOriginalTwoFlatIRPoolBook.Tested F J Z (h:=h) books u x φ) ∧
    ∀(h:ℕ)(x:∀i:Fin 3,RG17.Free R.family (grade i).val)(φ:Test 3),
      type_of% (WilsonOlderFreshSoftSocketStationPooledRestored.original F J Z φ simple bliss lead axes
        (WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid).2.1
        (WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid).1 (fun i=>by rw [paid.support i];norm_num)
        (fun i=>(paid.support i).le) color paid paths T h books priced x):=by
  obtain ⟨t,early,school⟩:=WilsonPhysicalHousedOpticalSchool.onBooks paid F J bliss lead axes (Fin 3) Z
    positive ratio stage 6
  obtain ⟨T,δ,dp,books,same⟩:=
    WilsonPhysicalWeakSameStation.books F simple bliss birth.day birth.rises birth.sale 6
  have priced:∀r,WilsonMovingForkWindowBooks.Priced F (books r):=fun r=>(same r).choose_spec.1.1
  have receipts:=WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid
  refine ⟨t,early,T,δ,dp,books,same,priced,fun h d=>school T h d books priced,?_,?_⟩
  · intro a u stop fac hl h x φ
    exact WilsonOriginalTwoFlatIRPoolBook.on_book F J Z stop fac bliss receipts.2.1 lead axes hl
      dp books priced h x φ
  · intro h x φ
    exact WilsonOlderFreshSoftSocketStationPooledRestored.original F J Z φ simple bliss lead axes
      receipts.2.1 receipts.1 (fun i=>by rw [paid.support i];norm_num) (fun i=>(paid.support i).le)
      color paid paths T h books priced x

end YM.Integration.WilsonOriginalObservedRoseBornBook
