import YM.Integration.WilsonOriginalMicroscopicStandingLabels
import YM.Integration.WilsonOriginalMicroscopicGuardedDated

/-! A predeclared common reporting calendar and its original Wilson columns
serve all later finite extraction accuracies on the same fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedStandingTrial
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical.Germ
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedNomination
open WilsonOriginalMicroscopicStandingLabels WilsonOriginalMicroscopicGuardedGridSchool
open OPE.Therm PhysicalNext OPE PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Climb.Bel R.family.book).Hierarchy}
  {Z:Trace.Terrace.Arch R.family}
local notation "C" => R.family

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((C).path.levels.budget j).supportExponent)(quote:Poetry (C).path.levels)(d:Fin 3→ℕ):
    ∃floor:ℕ→{η:ℝ //0<η}→ℕ,∀(r B:Fin 3→ℝ)(j m:Fin 3→ℕ),
    (∀a,Receipt F l (r a) (j a) (m a) (d a) (B a))→
    ∃Y:∀a:Fin 3,S.Field (d a)→ℕ×ℕ→(C).label (d a),
      (∀a,Press R F (l:=l) (r a) (j a) (m a) (d a) (B a) (Y a)) ∧
      ∀(v:∀a:Fin 3,S.Field (d a))(target:ℕ)(η:{e:ℝ //0<e}), (∀a,floor target η ≤ j a)→
      (∀a,Named R F (l:=l) (r a) (j a) (m a) (d a) target (B a) (v a) (Y a (v a))) ∧
      Finished R d j target (η:ℝ) (fun a=>budget R F (d a) (r a) (j a) (B a) (v a)) (fun a=>Y a (v a)):=by
  choose paid dated using fun x:ℕ×{η:ℝ //0<η}=>
    WilsonOriginalMicroscopicGuardedDated.original R simple shop wide quote d x.1 x.2.2
  choose stage seen using fun t (a:Fin 3)=>eventually_atTop.mp (WilsonOriginalMicroscopicStandingLabels.named R F (l:=l) simple wide (d a) t)
  let floor(t:ℕ)(η:{e:ℝ //0<e}):ℕ:=max (paid (t,η)) (Finset.univ.sup (stage t))
  refine ⟨floor,?_⟩
  intro r B j m school
  choose Y cash using fun a=>WilsonOriginalMicroscopicStandingLabels.before R F (school a)
  refine ⟨Y,cash,?_⟩
  intro v t η late
  have received (a:Fin 3):stage t a≤j a:=(Finset.le_sup (f:=stage t) (Finset.mem_univ a)).trans ((le_max_right ..).trans (late a))
  exact ⟨fun a=>seen t a (j a) (received a) (r a) (m a) (B a) (Y a) (cash a) (v a),
    dated (t,η) j (fun a=>(le_max_left ..).trans (late a)) _ _
      (fun a=>(cash a).2 (v a) |>.1)⟩

end YM.Integration.WilsonOriginalMicroscopicGuardedStandingTrial
end
