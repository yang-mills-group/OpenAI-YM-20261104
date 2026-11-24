import YM.Integration.WilsonMeasuredSignedActionReported
import YM.Integration.WilsonMeasuredSignedActionHeard

/-! The relative cost of a voted field can be absorbed using its measured
convergence alone. The original uncentered determining bank then fixes
the action on the projected limit. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionMeasuredLimit
open Function Filter Finset Set Spec Table Extraction Climb Trace Trace.Pilot Labels
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab Next.Rank OJoint
open WilsonMeasuredSignedActionAverage
open WilsonMeasuredSignedActionCourse (axis)
open WilsonMeasuredSignedActionProjected (posted)
open WilsonMeasuredPublicEntranceCommonColor (carried)
open WilsonPhysicalPositionAdmissible
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)
local notation "F₀" => C.labels.level 4
local notation "D₄" => (Bel C.book).Field 4

theorem original {I:Type*}{l:Filter I}[NeBot l]{w b:I→(F₀).Coeff}{a η:I→ℝ}{y:(F₀).Coeff}
    (positive:∀ᶠ i in l,0 ≤ a i)
    (enrolled:∀ᶠ i in l,∃k:ℝ,0 ≤ k ∧ (F₀).core (pool F₀ (w i))=(k:ℂ) • axis F₀)
    (pretest:Tendsto b l (𝓝 y))(rate:Tendsto η l (𝓝 0))(good:∀ᶠ i in l,0 ≤ η i)
    (paid:∀ᶠ i in l,let x:=(a i:ℂ) • (F₀).core (w i)
        (F₀).coeffSize (x-(F₀).core (b i))≤η i*(F₀).coeffSize x)
    {T:Module.End ℂ D₄}(native:Native C T)(identified:posted C y=T (stepField C)):
    ∃s:ℝ,0 ≤ s ∧ ∃c:ℂ,T (stepField C)=(s:ℂ) • stepField C+c • (Bel C.book).unit 4:=by
  have continuity:Continuous (fun x:(F₀).Coeff=>(F₀).coeffSize ((F₀).core x)):=by
    exact continuous_finsetSum _ fun j _=>((continuous_apply j).comp
      (F₀).core.continuous_of_finiteDimensional).norm
  have landed:=continuity.continuousAt.tendsto.comp pretest
  have near:=landed.eventually (gt_mem_nhds (lt_add_one ((F₀).coeffSize ((F₀).core y))))
  have bounded:∀ᶠi in l,(F₀).coeffSize ((F₀).core (b i))≤(F₀).coeffSize ((F₀).core y)+1:=
    near.mono (fun _ h=>le_of_lt h)
  obtain ⟨s,hs,hold⟩:=WilsonMeasuredSignedActionReported.converges F₀ positive enrolled pretest
    (WilsonMeasuredSignedActionReported.relative F₀ rate good bounded paid)
  exact WilsonMeasuredSignedActionProjected.original C T native y identified hs hold
end YM.Integration.WilsonMeasuredSignedActionMeasuredLimit
end
