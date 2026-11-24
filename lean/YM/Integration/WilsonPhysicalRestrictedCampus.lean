import YM.Integration.WilsonMeasuredPublicEntranceFullCampus
/-! Keep the original electorate, all original stages, the enrolled reporters,
and the genuine finite K inverse when restricting the purchased public master. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalRestrictedCampus
open Function Filter Finset MeasureTheory Lattice RG Wilson Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntranceFullCampus (School)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
theorem original {I O:Type}{D T t:ℕ}{d:I→Fin (D+1)}{e:I→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val}
    {field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target:ℕ}{ρ:I→{s:ℝ//0<s ∧ s<δ}}{f K:ℕ}
    (school:School F D T t d e books field M E tuition power target ρ f K)(pick:O→I):
    School F D T t (fun i=>d (pick i)) (fun i=>e (pick i)) books (fun i=>field (pick i))
      (fun i=>M (pick i)) (fun i=>E (pick i)) tuition power target (fun i=>ρ (pick i)) f K:=by
  obtain ⟨up,electrode,actual,paid⟩:=school
  refine ⟨up,fun p i=>electrode p (pick i),
    fun p i b old eta A x before arrived=>actual p (pick i) b old eta A x before arrived,?_⟩
  intro N per live L j
  obtain ⟨V,tags,home,registered,grant⟩:=paid N per live
  exact ⟨V,tags,home,registered,fun n select mode branch=>grant n (pick∘select) mode branch⟩

end YM.Integration.WilsonPhysicalRestrictedCampus
