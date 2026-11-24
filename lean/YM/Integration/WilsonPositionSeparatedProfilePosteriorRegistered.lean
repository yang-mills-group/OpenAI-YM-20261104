import YM.Integration.WilsonPositionSeparatedProfilePosteriorResponse
import YM.Integration.WilsonMatrixTicketLanesReportedReturn

/-! The exact bare experiment at the nominated MS reporting date, on the
original RG17 fields and the same real quadrature as the compact posterior. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfilePosteriorRegistered
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Tree Source Labels Precision PertExtension
open PhysicalNext.Repeat.Legato RG17 RG12 Pert.Asymptotics ConnectedActivityE6.Blaze.Thermal1020
open ConnectedActivityE6.Blaze.Thermal1020.Shared RGComparison.Core16 RGComparison.Core16.Spool
open WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesReportedPlating
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedSettlement
open private kernel_env from YM.Integration.WilsonHeldExteriorLaw
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Spec.Final R.family f S) (L:RG17.Layout F)

/-- The two physical presentations agree on each full gauge configuration. -/
theorem row (d:ℕ) (r:ℝ) (w:R.family.label d) (N p:ℕ) (age:R.family.ref d≤L.level r) (future:L.level r≤N)
    (o:Site (R.family.side (L.level r) p)) (U:Config G (R.family.side (L.level r) p)) :
    Push.Local.presented (R.family.localSection d) o (R.family.path.rep N p (L.level r)).p.threshold (L.shift d r w) U=
      R.family.O (L.level r) p (center R (L.level r) N p (atRef L d r (N,p) w)) o U := by
  rw [WilsonCoherentReportingFrame.arm,measured R F L d r w N p age future]
  have eq:(R.family.path.rep N p (L.level r)).p=R.family.path.levels.budget (L.level r):=(R.makes.wilson.represents N p (L.level r) future).vac
  rw [eq];rfl

private theorem linear {c f:Side} (D:StepData c f) (β:ℝ) (gate:D.patch.Branches D.kernel G)
    (V:Config G c) (Z:Config G f→ℂ) (cont:Continuous Z) (χ:ℂ→L[ℝ]ℝ) :
    (D.push β (fun U=>bare β U*χ (Z U)) V)/(D.push β (bare β) V)=
      χ ((D.push β (bare β) V)⁻¹ • D.push β (fun U=>bare β U • Z U) V) := by
  let C:=fun U=>D.density β U V*bare β U
  have eb:Envelope (bare β:Config G f→ℝ):=⟨(bare_cont β).measurable,(isCompact_univ.exists_bound_of_continuousOn (bare_cont β).continuousOn).imp fun _ a U=>a U (mem_univ U)⟩
  have es:Envelope C:=(kernel_env D β gate V).mul eb
  obtain ⟨B,hB⟩:=es.cost
  obtain ⟨K,hK⟩:=isCompact_univ.exists_bound_of_continuousOn cont.continuousOn
  have ec:Envelope (fun U=>D.density β U V • (bare β U • Z U)):=by
    simp_rw [smul_smul]
    refine ⟨es.meas.smul cont.measurable,B*K,?_⟩
    intro U;rw [norm_smul]
    exact mul_le_mul (hB U) (hK U (mem_univ U)) (norm_nonneg _) ((norm_nonneg _).trans (hB U))
  have hi:Integrable (fun U=>D.density β U V • (bare β U • Z U)) (prior G f):=ec.integrableC (prior G f)
  have num:D.push β (fun U=>bare β U*χ (Z U)) V=χ (D.push β (fun U=>bare β U • Z U) V):=by
    unfold StepData.push;rw [←χ.integral_comp_comm hi]
    apply integral_congr_ae;filter_upwards with U;rw [map_smul,map_smul];rfl
  rw [num,map_smul,smul_eq_mul,div_eq_inv_mul]

private theorem kernel {m b:ℕ} (p:ℕ) (e:m=b+1) :
    (WilsonMatrixTicketLanesReportedOneBlock.step R p e).patch.Branches (WilsonMatrixTicketLanesReportedOneBlock.step R p e).kernel G:=by
  subst m;exact (R.family.path.levels.blocks b p).branches

/-- Evaluating the signed real bare experiment is exactly evaluating the already
purchased independent comparison on this same true pin. -/
theorem assay {I:Type} [Fintype I] (d:I→ℕ) (r:ℝ) (w:∀i,R.family.label (d i)) (b N p:ℕ)
    (elected:L.level r=b+1) (age:∀i,R.family.ref (d i)≤L.level r) (future:L.level r≤N)
    (u:Directions G (R.family.side b p)) (o:I→Site (R.family.side (L.level r) p)) (χ:ℂ→L[ℝ]ℝ) :
    let D:=WilsonMatrixTicketLanesReportedOneBlock.step R p elected
    let m:=L.level r
    let β:=R.family.path.β N p m
    let g:=regulatorRun R.family N p m
    let X:=fun U=>∏i,Push.Local.presented (R.family.localSection (d i)) (o i) (R.family.path.rep N p m).p.threshold (L.shift (d i) r (w i)) U
    (D.push β (fun U=>bare β U*χ (X U)) (Parcel.Oven.slice u g))/(D.push β (bare β) (Parcel.Oven.slice u g))=
      χ (fresh R F L r d w b N p elected u o) := by
  intro D m β g X
  have price:g⁻¹^2=β:=by
    change (Real.sqrt β)⁻¹⁻¹^2=β
    have bp:0<β:=Overlay.beta_positive R.makes.wilson future
    rw [inv_inv,Real.sq_sqrt bp.le]
  have fx:X=fun U=>∏i,R.family.O m p (center R m N p (atRef L (d i) r (N,p) (w i))) (o i) U:=by
    funext U;exact Finset.prod_congr rfl fun i _=>row R F L (d i) r (w i) N p (age i) future (o i) U
  have cg:Continuous X:=by rw [fx];exact continuous_finsetProd _ fun i _=>R.family.continuousO m p (d i) _ (o i)
  rw [linear D β (kernel R p elected) _ X cg χ]
  unfold fresh Spool.spinVac
  dsimp only;change χ _=χ ((D.push (g⁻¹^2) (bare (g⁻¹^2)) (Parcel.Oven.slice u g))⁻¹ • D.push (g⁻¹^2) _ (Parcel.Oven.slice u g));rw [price,fx]

end YM.Integration.WilsonPositionSeparatedProfilePosteriorRegistered
