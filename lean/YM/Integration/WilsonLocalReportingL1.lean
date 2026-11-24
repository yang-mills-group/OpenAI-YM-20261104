import YM.Integration.WilsonLocalReportingDensityIntegral

/-! The actual price of the finite Taylor integral is relative to the
conditional absolute moment of the same registered signed group observable. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalReportingL1
open Function Filter Set Finset MeasureTheory Metric Lattice Wilson RG Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato WilsonReportingForestPivots WilsonPhysicalRegisteredForestAction
open WilsonLocalConditionalResidue WilsonLocalReportingChartIntegral WilsonLocalReportingChartFunctions
open WilsonLocalReportingExpense WilsonLocalInheritedDensity WilsonLocalReportingDensityIntegral MSbar.Heath OPE.Therm Pert.Asymptotics
open scoped Classical BigOperators Matrix.Norms.Frobenius Topology
variable {G:Gauge} {c f:Side} {S:StepData c f} {I:Type} [Fintype I]

theorem physical (T:Forest S.ratio) (B:Finset T.Free) {g:ℝ} (hg:0 < g)
    (z:WilsonLocalReportingChartIntegral.Field (G:=G) T B) :
    WilsonLocalConditionalResidue.position T B z.1 g (g⁻¹•z.2)=sampled T B z := by
  unfold WilsonLocalConditionalResidue.position sampled
  congr 1;funext i;change G.lieExp (g•(g⁻¹•z.2 i))=G.lieExp (z.2 i)
  rw [smul_smul,mul_inv_cancel₀ hg.ne',one_smul]

theorem abs_entry (P:ChartRatio G) (T:Forest S.ratio) (B:Finset T.Free) (C:Set (Config G f))
    (ρ H:Config G f→ℝ) (hρ:∀U,0 ≤ ρ U) (z:WilsonLocalReportingChartIntegral.Field (G:=G) T B) :
    ‖entry P T B C (fun U=>ρ U*H U) z‖=entry P T B C (fun U=>ρ U*‖H U‖) z := by
  by_cases live:sampled T B z∈C
  · simp only [entry,Set.indicator_of_mem live,norm_mul,Real.norm_of_nonneg (Chart.jacobian_nonneg _),
      Real.norm_of_nonneg (hρ _)]
  · simp only [entry,Set.indicator_of_notMem live,mul_zero,norm_zero]

theorem accepted (R:Run G) (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (p:ℕ) {ε r:ℝ}
    (ep:0 < ε) (rv:r ≤ J.r) :
    ∀ᶠm:ℕ in atTop,∀N,m < N→∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per)) (H:Config G (R.family.side (m+1) per)→ℝ),
    let B:=incident R T d o
    let C:=cold R m per d o
    let g:=regulatorRun R.family N per (m+1)
    let ρ:=actualConditionalDensity R.family N per m V
    let a:=entry P T B C (fun U=>ρ U*H U)
    let b:=proposal P p R N per m V T B g C H
    ∀ᵐ z ∂law G T B r, ‖a z-b z‖ ≤ ε*g^p*‖a z‖ := by
  filter_upwards [WilsonLocalReportingSpectator.original R simple slow P hp J clear d p ep] with m insured N live per o T V H
  let C:=cold R m per d o
  let B:=incident R T d o
  let g:=regulatorRun R.family N per (m+1)
  let ρ:=actualConditionalDensity R.family N per m V
  have gp:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  filter_upwards [ball_ae (G:=G) T B r] with z hz
  let U:=sampled T B z
  let X:=g⁻¹•z.2
  change ‖entry P T B C (fun U=>ρ U*H U) z-proposal P p R N per m V T B g C H z‖ ≤
    ε*g^p*‖entry P T B C (fun U=>ρ U*H U) z‖
  by_cases h:sampled T B z∈C
  · have gX:g•X=z.2:=by dsimp only [X];rw [smul_smul,mul_inv_cancel₀ gp.ne',one_smul]
    have inC:WilsonLocalConditionalResidue.position T B z.1 g X∈C:=by rw [physical T B gp z];exact h
    have got:admitted R J d m per o T z.1 g X := ⟨gX ▸ (mem_ball_zero_iff.mp hz).le.trans rv,inC⟩
    have weight_eq:WilsonLocalConditionalResidue.weight P ρ T B z.1 g X=Chart.jacobian P z.2*ρ U:=by
      rw [WilsonLocalConditionalResidue.weight,gX,physical T B gp z]
    have aeq:entry P T B C (fun U=>ρ U*H U) z=WilsonLocalConditionalResidue.weight P ρ T B z.1 g X*H U:=by
      rw [entry,Set.indicator_of_mem h,weight_eq,mul_assoc]
    have beq:proposal P p R N per m V T B g C H z=model P p R N per m V T B z.1 g X*H U := by rw [proposal,if_pos h]
    rw [aeq,beq]
    exact insured N live per o T V z.1 X got ℝ (H U)
  · have aeq:entry P T B C (fun U=>ρ U*H U) z=0:=by rw [entry,Set.indicator_of_notMem h,mul_zero]
    have beq:proposal P p R N per m V T B g C H z=0:=by rw [proposal,if_neg h]
    rw [aeq,beq];simp

theorem original (R:Run G) (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (p:ℕ) {ε r:ℝ}
    (ep:0 < ε) (pr:0 < r) (sr:r < Chart.small G P) (rv:r ≤ J.r) :
    ∀ᶠm:ℕ in atTop,∀N,m < N→∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per)) (H:Config G (R.family.side (m+1) per)→ℝ),
    Envelope H→GaugeInvariant H→
    let B:=incident R T d o
    let C:=cold R m per d o
    let g:=regulatorRun R.family N per (m+1)
    let μ:=law G T B r
    let b:=proposal P p R N per m V T B g C H
    Integrable b μ ∧ |actualAverage R.family (N:=N) (C.indicator H) V-(∫z,b z ∂μ)| ≤
      ε*g^p*actualAverage R.family (N:=N) (C.indicator (fun U=>‖H U‖)) V := by
  filter_upwards [accepted R simple slow P hp J clear d p ep rv,
    WilsonLocalReportingChartIntegral.original R simple slow J clear P hp pr sr d] with m pay read N live per o T V H eh hi
  let B:=incident R T d o
  let C:=cold R m per d o
  let g:=regulatorRun R.family N per (m+1)
  let ρ:=actualConditionalDensity R.family N per m V
  have hc:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  obtain ⟨h,h0,lower⟩:=WilsonHeldExteriorLaw.upper_floor R N per m live
  have ew:Envelope ρ:=(WilsonHeldExteriorLaw.regularity R N per m live V ((R.family.path).rep N per (m+1))
    (((R.family.path).rep N per (m+1)).envelope (R.makes.wilson.represents N per (m+1) live).good) h0 lower).1
  have en:Envelope (fun U=>‖H U‖):=⟨eh.meas.norm,eh.cost.choose,fun U=>by simpa only [norm_norm] using eh.cost.choose_spec U⟩
  have inv:GaugeInvariant (fun U=>‖H U‖):=fun a U=>congrArg norm (hi a U)
  have absfun: (fun z=>‖entry P T B C (fun U=>ρ U*H U) z‖)=entry P T B C (fun U=>ρ U*‖H U‖):=
    funext (abs_entry P T B C ρ H (fun U=>(WilsonLocalInheritedRatio.positive R N per m live V U).2.le))
  have hpay:=difference (law G T B r) (integrable P hp T B hc (ew.mul eh) pr sr)
    (proposal_m P p R N per m live V T B g hc eh.meas) (pay N live per o T V H)
  rw [absfun] at hpay
  exact ⟨hpay.1,((read N live per o T V H eh hi) ▸ (read N live per o T V _ en inv) ▸ hpay.2)⟩

end YM.Integration.WilsonLocalReportingL1
