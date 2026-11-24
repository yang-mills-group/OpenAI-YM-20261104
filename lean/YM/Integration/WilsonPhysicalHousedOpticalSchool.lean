import YM.Integration.WilsonIndependentMeasuredOpticalSchool
import YM.Integration.WilsonMeasuredPublicEntrancePublicFaculty
import YM.Integration.WilsonAddressedPublicCardBooks

/-! The original optical sale on the same previously funded exact-radius book as the public moving detector. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalHousedOpticalSchool
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedMixedMasterSchool (field)
open WilsonMeasuredPublicEntrancePanelSchool (Registered)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{simple:G.Simple}

theorem onBooks {axis:Axis}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}{T:Campaign R}{W:Campaign.Pillars R T}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε s R T W)
    {v:Extraction.Order}{S:Table R.family.book}(F:Final R.family v S){l:Ultrafilter (ℕ×ℕ)}
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}(J:ℝ→PhysMS.tower S)
    (bliss:Bliss F l z H)(lead:Leading F J)(axes:∀g,∀ᶠr in trail,Frame.obedient F H (J r) g)
    (I:Type)[Fintype I][Nonempty I](Z:WilsonPrescription G){n:ℕ}(positive:0<n)(ratio:Z.run.ratio=(3:ℕ)^n)
    (stage D:ℕ) :
    ∃t ≥ D+3,∀(T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
      (books:(r:{r:ℝ // 0<r ∧ r<δ})→Book F (l:=l) H z D T r.val),
      (∀r,WilsonMovingForkWindowBooks.Priced F (books r)) → ∀
      (y:∀i,(Spin.comparator R.family.book).Field (d i).val)(x:∀i,RG17.Free R.family (d i).val),
      ∃grant:Registered F D T h t d books (field F J Z D T d y x books),type_of%
        (WilsonIndependentMeasuredOpticalSchool.original F Z simple bliss
          (WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid).2.1 (axis:=axis) (ε:=Stroke.epsilonR)
          paid.nested.2 positive ratio stage grant) := by
  classical
  have costs:=WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid
  have therm:OPE.Therm.Poetry R.family.path.levels:=by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,fund,_⟩:=paid.originalSchool
    exact fund.2.1.paid.stoves
  obtain ⟨t,head,school⟩:=WilsonReflectedMixedMasterSchool.original (I:=I) F J Z simple bliss costs.2.1
    costs.1 (fun i=>by rw [paid.support i];norm_num) (fun i=>(paid.support i).le) therm lead axes D
  refine ⟨t,head,?_⟩
  intro T h d δ books admitted y x
  have grant:=WilsonMeasuredPublicEntrancePanelSchool.received F
    (WilsonReflectedMixedPrescribedSchool.original F J Z simple bliss costs.2.1 (school T h d y x books admitted))
  exact ⟨grant,WilsonIndependentMeasuredOpticalSchool.original F Z simple bliss
    costs.2.1 (axis:=axis) (ε:=Stroke.epsilonR) paid.nested.2 positive ratio stage grant⟩

theorem original {axis:Axis}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}{T:Campaign R}{W:Campaign.Pillars R T}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε s R T W)
    {v:Extraction.Order}{S:Table R.family.book}(F:Final R.family v S){l:Ultrafilter (ℕ×ℕ)}
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}(J:ℝ→PhysMS.tower S)
    (bliss:Bliss F l z H)(lead:Leading F J)(axes:∀g,∀ᶠr in trail,Frame.obedient F H (J r) g)
    (I:Type)[Fintype I][Nonempty I](Z:WilsonPrescription G){n:ℕ}(positive:0<n)(ratio:Z.run.ratio=(3:ℕ)^n)
    (stage D:ℕ) :
    ∃t ≥ D+3,∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(r:{r:ℝ // 0<r ∧ r<δ})→Book F (l:=l) H z D T r.val,
      (∀r,WilsonAddressedPublicCardBooks.Housed F (books r)) ∧ ∀(h:ℕ)(d:I→Fin (D+1))
      (y:∀i,(Spin.comparator R.family.book).Field (d i).val)(x:∀i,RG17.Free R.family (d i).val),
      ∃grant:Registered F D T h t d books (field F J Z D T d y x books),type_of%
        (WilsonIndependentMeasuredOpticalSchool.original F Z simple bliss
          (WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid).2.1 (axis:=axis) (ε:=Stroke.epsilonR)
          paid.nested.2 positive ratio stage grant) := by
  obtain ⟨t,head,school⟩:=onBooks paid F J bliss lead axes I Z positive ratio stage D
  obtain ⟨T,δ,positive,books,housed⟩:=WilsonAddressedPublicCardBooks.original F simple bliss D
  exact ⟨t,head,T,δ,positive,books,housed,fun h d=>school T h d books (fun r=>(housed r).1)⟩

end YM.Integration.WilsonPhysicalHousedOpticalSchool
