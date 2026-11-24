import YM.Integration.WilsonCenteredFourPhysicalSchool
import YM.Integration.WilsonPublicOutputRegulators
import YM.Integration.WilsonPublicForkPaid
import YM.Integration.WilsonOriginalBlissFieldLift

/-! The exact submitted two grade-four directions and all 22 output directions on
the original selected layout. The independent experiment supplies the coefficients
of the microscopic signed test, including its unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourCutoffRows
open Function Filter Set MeasureTheory Extraction Table Spec OPE OPE.Orbits RG17
open PhysMS Trace.Pilot Trace.Terrace EveryPhase Climb PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register XSpace XSpace.Normalize RG12 SharpGram Maxwell
open WilsonPositionHomogeneousFrame WilsonMSDictionaryVector WilsonViewerElectedHierarchy WilsonLimitConstruction
open WilsonMacroscopicRichPositionRows WilsonMacroscopicRichTwoDatePivot WilsonMacroscopicRichSignedAmplitude WilsonMatrixTicketLanesSmearedPivot
open scoped Classical Topology BigOperators
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
local notation "d₄" => (fun _:Fin 2=>4)

theorem cost {I:Type}[Fintype I](X:I→External R.family S)(pub:Free R.family 4≃ₗ[ℂ]S.Field 4)
    (e:Free R.family 4)(seen:I→ℂ):
    WilsonCenteredFourFiniteSlate.invoice F X pub e seen (fun j=>(X j).charge F 4 (pub e))
      (fun b j=>(X j).charge F 4 (pub (WilsonMSDictionaryVector.basis R.family 4 b)))=
        ‖seen-(fun j=>(X j).charge F 4 (pub e))‖:=by
  let T:Free R.family 4→ₗ[ℂ](I→ℂ):=(LinearMap.pi (fun j=>(X j).charge F 4)).comp pub.toLinearMap
  let B:=WilsonMSDictionaryVector.basis R.family 4
  have eval:T e=∑b,B.repr e b • T (B b):=by
    conv_lhs=>rw [←B.sum_repr e]
    simp only [map_sum,map_smul]
  change ‖seen-T e‖+‖T e-∑b,B.repr e b • T (B b)‖+
    ∑b,‖B.repr e b‖*‖T (B b)-T (B b)‖=_
  rw [←eval]
  simp only [sub_self,norm_zero,mul_zero,Finset.sum_const_zero,add_zero]
  rfl

theorem original {T:Campaign R}{W:Campaign.Pillars R T}{κ:ℝ}{simple:G.Simple}
    (fund:FundedOriginalProperties.{u} simple κ W){course:Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {Y:(Bel R.family.book).Hierarchy}{arch:Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}(run:Selected.{u} F course Q J Y arch l simple cohort)
    (B:Profiles R 4)(w:B.probes.index→Atom (R:=R) 4)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid 4 (w j))
    (level:ℝ→ℕ)(grow:Tendsto level trail atTop)(shift:∀ d,ℝ→R.family.label d≃ₗ[ℂ]R.family.label d)
    (g:ℝ→ℝ)(hg:Coupling G g)(K:Set (Points 2))(compact:IsCompact K)(spread:K⊆conf 2)
    (A:ℕ)(ap:0<A):
    let layout:=WilsonOriginalBlissObserved.layout F run.bliss J level shift
    let column:=WilsonOriginalBlissFieldLift.column (S:=S) arch level shift
    ∀ᶠr in trail,let t:=r/((g r)^A)^2
    ∀(tp:0<t)(v:Fin 2→Free R.family 4)(ψ:Test 2),tsupport ψ⊆K→
    let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued tp
    let pub:=homogeneous F J Z r 4
    let u:=fun i=>pub (v i)
    let seen:=fun j=>appeared F (d:=d₄) u (X j) r ψ
    let ins:=fun i=>column 4 r (u i)
    let out:=fun b=>column 4 r (pub (WilsonMSDictionaryVector.basis R.family 4 b))
    ∀(value:ℝ→Free R.family 4)(δ:ℝ),
      (∃ᶠs:ℝ in atTop,f.late fun N p=>
        ‖WilsonPublicOutputRegulators.contrast F layout X d₄ ins out r ψ (value s) (N,p)‖≤δ)→
      ∃ᶠs:ℝ in atTop,WilsonCenteredFourFiniteSlate.invoice F X pub (value s) seen
        (fun j=>(X j).charge F 4 (pub (value s)))
        (fun b j=>(X j).charge F 4 (pub (WilsonMSDictionaryVector.basis R.family 4 b)))≤δ:=by
  obtain ⟨_,_,_,ready⟩:=WilsonPublicForkPaid.original F fund course run.phases run.facilities
    run.bliss run.matrix Q run.foundation J Z.store run.leading Z run.obeys d₄ 4 B w issued g hg K compact spread
  intro layout column
  filter_upwards [ready A ap,grow.eventually_ge_atTop (R.family.ref 4),self_mem_nhdsWithin] with r rows live rp
  intro t tp v ψ inside X pub u seen ins out value δ signed
  obtain ⟨packed,integrable,_⟩:=rows tp v ψ inside
  have field:=WilsonOriginalBlissFieldLift.field F arch run.bliss J level shift 4 r
  have received:=WilsonPublicOutputRegulators.original F J Z layout X d₄ ins out r ψ u
    (fun i=>field (u i)) (fun _=>live) (fun i=>field (pub (WilsonMSDictionaryVector.basis R.family 4 i)))
    live rp packed integrable value δ signed
  exact received.mono fun s bound=>(cost F X pub (value s) seen).le.trans bound

end YM.Integration.WilsonCenteredFourCutoffRows
