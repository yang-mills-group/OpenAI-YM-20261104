import YM.Integration.WilsonLocalReportingL1

/-! Local Wilson and Haar factors which can multiply any positive retained
driver on this same sampled exterior. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalConditionalWilsonFactor
open Function Filter Finset Set MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato WilsonReportingForestPivots WilsonLocalConditionalResidue WilsonLocalReportingChartIntegral
open WilsonLocalReportingChartFunctions WilsonLocalReportingExpense WilsonLocalInheritedDensity MSbar.Heath OPE.Therm Pert.Asymptotics
open scoped Classical BigOperators Matrix.Norms.Frobenius Topology
variable {G:Gauge} {c f:Side} {S:StepData c f} {I:Type} [Fintype I]

def factor (P:ChartRatio G) (p:ℕ) (β g:ℝ) (T:Forest S.ratio) (B:Finset T.Free) (z:Field (G:=G) T B) :=
  let Y:=WilsonLocalConditionalResidue.position T B z.1 g 0
  Chart.jacobian P (0:↥(moving T B)→G.Color)*bare β Y/bare β (sampled T B z)*
    Real.exp (score P p β g T B z.1 (g⁻¹•z.2) 0)

theorem regular (P:ChartRatio G) (p:ℕ) (β g:ℝ) (T:Forest S.ratio) (B:Finset T.Free) : Measurable (factor P p β g T B) := by
  let A:=Field (G:=G) T B
  have h0:=position_m T B (M:=A) measurable_fst (measurable_const (a:=(0:↥(moving T B)→G.Color))) g
  have hx:Measurable (fun z:A=>g⁻¹•z.2):=(continuous_const_smul g⁻¹).measurable.comp measurable_snd
  exact ((measurable_const.mul ((bare_cont β).measurable.comp h0)).div ((bare_cont β).measurable.comp (sampled_m T B))).mul
    (score_m P p β g T B measurable_fst hx measurable_const).exp

theorem nonnegative (P:ChartRatio G) (p:ℕ) (β g:ℝ) (T:Forest S.ratio) (B:Finset T.Free) (z:Field (G:=G) T B) :
    0 ≤ factor P p β g T B z :=
  mul_nonneg (div_nonneg (mul_nonneg (Chart.jacobian_nonneg _) (bare_pos _ _).le) (bare_pos _ _).le) (Real.exp_pos _).le

theorem regroup (a k init u y h:ℝ) (hu:u≠0) (hy:y≠0) :
    a*k*init/y*h=(a*init/u*h)*(k*u/y) := by field_simp [hu,hy]

theorem at_sample (P:ChartRatio G) (ρ:Config G f→ℝ) (T:Forest S.ratio) (B:Finset T.Free) {g:ℝ} (hg:0 < g)
    (z:Field (G:=G) T B) : WilsonLocalConditionalResidue.weight P ρ T B z.1 g (g⁻¹•z.2)=Chart.jacobian P z.2*ρ (sampled T B z) := by
  rw [WilsonLocalConditionalResidue.weight,WilsonLocalReportingL1.physical T B hg z,smul_smul,mul_inv_cancel₀ hg.ne',one_smul]

theorem restore (P:ChartRatio G) (p:ℕ) (R:Run G) (N per m:ℕ) (hm:m < N) (V:Config G (R.family.side m per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free) {g:ℝ} (gp:0 < g) (z:Field (G:=G) T B) :
    model P p R N per m V T B z.1 g (g⁻¹•z.2)=factor P p (R.family.path.β N per (m+1)) g T B z*actualConditionalDensity R.family N per m V (sampled T B z) := by
  let β:=R.family.path.β N per (m+1)
  let U:=sampled T B z
  let q:=(R.family.path.rep N per m).eval V
  have hq:0 < q:=Multi.AxisShift.chosen_positive R.makes.wilson hm.le V
  have gu:0 < bare β U:=bare_pos _ _
  unfold model factor;dsimp only;rw [WilsonLocalReportingL1.physical T B gp z,WilsonLocalInheritedRatio.split]
  exact regroup _ _ _ _ _ _ gu.ne' hq.ne'

theorem cancel (j f w δ:ℝ) (jp:0 ≤ j) (wp:0 < w) (h:|j*w-f*w| ≤ δ*|j*w|) :
    |j-f| ≤ δ*j := by
  rw [←sub_mul,abs_mul,abs_of_pos wp,abs_of_nonneg (mul_nonneg jp wp.le),←mul_assoc] at h
  exact le_of_mul_le_mul_right h wp

theorem billed {x y j f w δ:ℝ} (jp:0 ≤ j) (wp:0 < w) (a:x=j*w) (b:y=f*w)
    (invoice:‖x•(1:ℝ)-y•(1:ℝ)‖ ≤ δ*‖x•(1:ℝ)‖) : |j-f| ≤ δ*j := by
  apply cancel j f w δ jp wp
  simpa only [a,b,smul_eq_mul,mul_one,Real.norm_eq_abs] using invoice

theorem allowed (R:Run G) (J:Voice G) (d:I→ℕ) (m per:ℕ) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) {g r:ℝ} (gp:0 < g) (rv:r ≤ J.r)
    (z:Field (G:=G) T (incident R T d o)) (hz:z.2∈ball 0 r) (hc:sampled T (incident R T d o) z∈cold R m per d o) :
    admitted R J d m per o T z.1 g (g⁻¹•z.2) := by
  constructor
  · rw [smul_smul,mul_inv_cancel₀ gp.ne',one_smul];exact (mem_ball_zero_iff.mp hz).le.trans rv
  · rw [WilsonLocalReportingL1.physical T (incident R T d o) gp z];exact hc

theorem priced (R:Run G) (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (p:ℕ) {ε r:ℝ}
    (ep:0 < ε) (rv:r ≤ J.r) :
    ∀ᶠm:ℕ in atTop,∀N,m < N→∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio),
    let B:=incident R T d o
    let g:=regulatorRun R.family N per (m+1)
    let β:=R.family.path.β N per (m+1)
    ∀z:Field (G:=G) T B,z.2∈ball 0 r→sampled T B z∈cold R m per d o→
    |Chart.jacobian P z.2-factor P p β g T B z| ≤ ε*g^p*Chart.jacobian P z.2 := by
  filter_upwards [WilsonLocalReportingSpectator.original R simple slow P hp J clear d p ep] with m bill N hm per o T
  dsimp only;intro z hz hC
  let B:=incident R T d o
  let β:=R.family.path.β N per (m+1)
  let g:=regulatorRun R.family N per (m+1)
  let U:=sampled T B z
  let V:Config G (R.family.side m per):=1
  let w:=actualConditionalDensity R.family N per m V U
  have gp:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson hm))
  have got:=allowed R J d m per o T gp rv z hz hC
  let μ:=actualConditionalDensity R.family N per m V
  have qA:=at_sample P μ T B gp z
  have qB:=restore P p R N per m hm V T B gp z
  exact billed (Chart.jacobian_nonneg _) (WilsonLocalInheritedRatio.positive R N per m hm V U).2
    qA qB (bill N hm per o T V z.1 (g⁻¹•z.2) got ℝ 1)

end YM.Integration.WilsonLocalConditionalWilsonFactor
