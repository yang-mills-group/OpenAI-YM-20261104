import YM.Integration.WilsonLocalConditionalWilsonFactor
import YM.Integration.WilsonCoherentRetainedDriver

/-! The finite retained action with its genuine exterior marginal and its
own local Haar/Wilson Taylor factor. No untruncated fine-state density
appears in the sampled part of this fitted value. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalRetainedReportingWeight
open Function Filter Finset Set MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction WilsonReportingForestPivots
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLocalConditionalWilsonFactor WilsonCoherentForestMeasure WilsonCoherentForestReadout WilsonCoherentMeasuredChart
open scoped Classical BigOperators Matrix.Norms.Frobenius Topology
variable {G:Gauge} {I:Type} [Fintype I]

def adjusted (P:ChartRatio G) (p:ℕ) (R:Run G) {N per m:ℕ} (live:m+1 < N) (grade:ℕ)
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (V:Config G (R.family.side m per)) (z:Sample T B G) : ℝ :=
  let β:=R.family.path.β N per (m+1)
  let g:=regulatorRun R.family N per (m+1)
  WilsonCoherentRetainedDriver.value R live grade T B V z*(factor P p β g T B z/Chart.jacobian P z.2)

theorem multiply {j f w t d:ℝ} (hj:0 < j) (hf:0 ≤ f) (hw:0 ≤ w) (ht:0 ≤ t) (td:t ≤ 2*w)
    (once:3*d ≤ 1) (old:|w-t| ≤ d*w) (fresh:|j-f| ≤ d*j) :
    0 ≤ t*(f/j) ∧ t*(f/j) ≤ 2*w ∧ |w-t*(f/j)| ≤ 3*d*w := by
  have ratio:|1-f/j| ≤ d := by
    rw [show 1-f/j=(j-f)/j by field_simp [hj.ne'],abs_div,abs_of_pos hj];exact (div_le_iff₀ hj).mpr fresh
  have budget:|w-t*(f/j)| ≤ 3*d*w := calc
    _ = |(w-t)+t*(1-f/j)| := by congr 1;ring
    _ ≤ |w-t|+t*|1-f/j|:= (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_of_nonneg ht])
    _ ≤ d*w+(2*w)*d := add_le_add old (mul_le_mul td ratio (abs_nonneg _) (by positivity))
    _=_:=by ring
  have cap:=mul_le_mul_of_nonneg_right once hw
  have low : -((3*d)*w) ≤ w-t*(f/j) :=(abs_le.mp budget).1
  exact ⟨mul_nonneg ht (div_nonneg hf hj.le),by linarith only [cap,low],budget⟩

theorem fee_positive (P:ChartRatio G) (hp:LocalRatio P) (p:ℕ) (β g:ℝ) {c f:Side} {S:StepData c f}
    (T:Forest S.ratio) (B:Finset T.Free) (z:Sample T B G) : 0 < factor P p β g T B z := by
  have anchor:0 < Chart.jacobian P (0:↥(moving T B)→G.Color) := by
    apply Finset.prod_pos;intro e _;change 0 < Chart.fee P 0
    rw [WilsonConditionalTaylorThermalLocalHaar.anchor P hp];exact hp.scale
  exact mul_pos (div_pos (mul_pos anchor (bare_pos _ _)) (bare_pos _ _)) (Real.exp_pos _)

theorem denominator {j f d:ℝ} (hj:0 ≤ j) (hf:0 < f) (small:|j-f| ≤ d*j) : 0 < j := by
  by_contra! h
  have z:=le_antisymm h hj
  rw [z,zero_sub,abs_neg,abs_of_pos hf,mul_zero] at small
  exact hf.not_ge small

theorem priced (R:Run G) (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (p grade:ℕ) (order:p+5 ≤ grade)
    {ε r:ℝ} (ep:0 < ε) (rv:r ≤ J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1 < N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per)),
    let B:=incident R T d o
    let g:=regulatorRun R.family N per (m+1)
    let w:=actualConditionalDensity R.family N per m V
    let t:=adjusted P p R live grade T B V
    Measurable t ∧ ∀z∈panel R m per d o T r,0 ≤ t z ∧ t z ≤ 2*w (state T B z) ∧
      |w (state T B z)-t z| ≤ ε*g^p*w (state T B z) := by
  let η:=min (1/3) (ε/3)
  have hn:0 < η:=lt_min (by norm_num) (by positivity)
  have rise:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [WilsonLocalConditionalWilsonFactor.priced R simple slow P hp J clear d p hn rv,
    WilsonCoherentRetainedDriver.purchased R simple marks fees slow d p grade order hn,rise.eventually_ge_atTop (2:ℝ)] with
    m fresh old hot N live per o T V
  dsimp only
  let B:=incident R T d o
  let β:=R.family.path.β N per (m+1)
  let g:=regulatorRun R.family N per (m+1)
  let w:=actualConditionalDensity R.family N per m V
  have wp:∀U,0 < w U:=fun U=>(WilsonLocalInheritedRatio.positive R N per m live.le V U).2
  have gp:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live.le))
  have minβ:R.family.path.levels.clock.hatBeta (m+1)/2 ≤ β:=(R.makes.wilson.represents N per (m+1) live.le).band.1
  have hj:2 ≤ R.family.path.levels.clock.hatBeta (m+1):=hot
  have gle:g ≤ 1:=inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (show 1 ≤ β by linarith only [minβ,hj]))
  have cube:3*(η*g^p) ≤ 1:=by
    have a:=mul_le_mul_of_nonneg_left (pow_le_one₀ gp.le gle (n:=p)) hn.le
    have b:η ≤ 1/3:=min_le_left ..;linarith only [a,b]
  have fare:3*(η*g^p) ≤ ε*g^p:=by
    have h:η ≤ ε/3:=min_le_right ..
    rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (by linarith only [h]) (pow_nonneg gp.le _)
  obtain ⟨mt,receipt⟩:=old N live per o T V
  refine ⟨mt.mul ((regular P p β g T B).div ((Chart.Ratio.jacobian_meas hp).comp measurable_snd)),?_⟩
  intro z hz
  have paid:=fresh N live.le per o T z hz.1 hz.2
  have funded:=receipt z
  have ja:=denominator (Chart.jacobian_nonneg _) (fee_positive P hp p β g T B z) paid
  have bought:=multiply ja (nonnegative P p β g T B z) (wp _).le funded.2.1 funded.2.2.1
    cube funded.2.2.2 paid
  exact ⟨bought.1,bought.2.1,bought.2.2.trans (mul_le_mul_of_nonneg_right fare (wp _).le)⟩

end YM.Integration.WilsonLocalRetainedReportingWeight
