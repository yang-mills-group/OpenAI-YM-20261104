import YM.Integration.WilsonLocalRetainedAnchor
import YM.Integration.WilsonLocalHeldKernelIntegral

/-! Replacing the old fine action by its funded finite action at the
sampled angles while keeping the exact old action at fixed exterior pivots. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalAnchoredReportingFactor
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonCoherentForestMeasure WilsonLocalConditionalWilsonFactor
open WilsonCoherentMeasuredChart
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

def multiplier (P:ChartRatio G) (q:ℕ) (R:Run G) {N per m:ℕ} (live:m+1<N) (grade:ℕ)
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free) (z:Sample T B G) : ℝ :=
  factor P q (R.family.path.β N per (m+1)) (regulatorRun R.family N per (m+1)) T B z*
    WilsonLocalRetainedAnchor.ratio R live grade T B z

theorem product {j f k δ:ℝ} (j0:0≤j) (f0:0≤f) (d1:δ≤1)
    (a:|j-f|≤δ*j) (b:|1-k|≤δ) : |j-f*k|≤3*δ*j := by
  have cut:=mul_le_mul_of_nonneg_right d1 j0
  have jf:= (abs_le.mp a).1
  have grow:f≤2*j:=by linarith only [cut,jf]
  calc |j-f*k| = |(j-f)+f*(1-k)| := by congr 1;ring
       _ ≤ |j-f|+f*|1-k| := (abs_add_le ..).trans_eq (by rw [abs_mul,abs_of_nonneg f0])
       _ ≤ δ*j+(2*j)*δ := add_le_add a (mul_le_mul grow b (abs_nonneg _) (by positivity))
       _ = 3*δ*j := by ring

theorem purchased (R:Run G) (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (order:q+5 ≤ grade)
    {ε r:ℝ} (ep:0 < ε) (rv:r ≤ J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio),
    let B:=incident R T d o
    let g:=regulatorRun R.family N per (m+1)
    let Φ:=multiplier P q R live grade T B
    Measurable Φ ∧ ∀z∈panel R m per d o T r, |Chart.jacobian P z.2-Φ z|≤ε*g^q*Chart.jacobian P z.2 := by
  let η:=min 1 (ε/3)
  have hpη:0<η:=lt_min zero_lt_one (by positivity)
  have rises:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [WilsonLocalRetainedAnchor.purchased R simple marks fees slow d q grade order hpη,
    priced R simple slow P hp J clear d q hpη rv,rises.eventually_ge_atTop (2:ℝ)] with m incoming cost hot N live per o T
  intro B g Φ
  let β:=R.family.path.β N per (m+1)
  obtain ⟨mr,ledger⟩:=incoming N live per o T
  refine ⟨(regular P q β g T B).mul mr,?_⟩
  have heat:R.family.path.levels.clock.hatBeta (m+1)/2≤β:=(R.makes.wilson.represents N per (m+1) live.le).band.1
  change 2 ≤ R.family.path.levels.clock.hatBeta (m+1) at hot
  have gle:g≤1:=inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (show 1≤β by linarith only [heat,hot]))
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have η₁:η*g^q≤1:=(mul_le_mul_of_nonneg_left (pow_le_one₀ gp gle (n:=q)) hpη.le).trans
    ((mul_one η).le.trans (min_le_left ..))
  have ηε:3*η≤ε:=by have h:η≤ε/3:=min_le_right ..;linarith only [h]
  intro z hz
  refine (product (Chart.jacobian_nonneg _) (nonnegative P q β g T B z) η₁
    (cost N live.le per o T z hz.1 hz.2) (ledger z).2).trans ?_
  exact mul_le_mul_of_nonneg_right ((mul_assoc (3:ℝ) η (g^q)).symm.le.trans
    (mul_le_mul_of_nonneg_right ηε (pow_nonneg gp _))) (Chart.jacobian_nonneg _)

theorem field (P:ChartRatio G) (q:ℕ) (R:Run G) {N per m:ℕ} (live:m+1<N) (grade:ℕ)
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free) (z:Sample T B G) (D H:ℝ) :
    let Q:=R.family.path.rep N per (m+1)
    let A:=approximation R (p:=per) live grade
    let U:=state T B z
    let U0:=state T B (z.1,0)
    let f:=factor P q (R.family.path.β N per (m+1)) (regulatorRun R.family N per (m+1)) T B z
    multiplier P q R live grade T B z*(D*Q.eval U*H)= f*(Q.eval U0/A.eval U0)*(D*A.eval U*H) := by
  intro Q A U U0 f
  have pos:0 < Q.eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live.le U
  change (f*((Q.eval U0/A.eval U0)*(A.eval U/Q.eval U)))*(D*Q.eval U*H)=_
  generalize Q.eval U0/A.eval U0=a
  field_simp [pos.ne']

end YM.Integration.WilsonLocalAnchoredReportingFactor
