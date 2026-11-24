import YM.Integration.WilsonMatrixTicketLanesConnectedForecast
import YM.Integration.WilsonMatrixTicketLanesRetainedSpatialRate
import YM.Integration.WilsonMatrixTicketLanesReportedAccuracy
import YM.Integration.WilsonCoherentInheritedSpool
import YM.RG01.Slack

/-! Every-order spatial decay of the genuine positive, normalized, one-step compact covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedPositive
open Function Filter Finset Real Lattice Gauge RG Wilson Tree Precision PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Silk RGComparison.Core16.Parcel
open RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet Pert.Asymptotics
open WilsonMatrixTicketLanesReflectedGauge WilsonMatrixTicketLanesConnectedBudget
open WilsonMatrixTicketLanesConnectedForecast Next.Rank
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)
local notation "β" => R.family.path.levels.clock.hatBeta

private theorem sum (a : Roll) (k : ℕ) {D g : ℝ} (gp : 0 ≤ g) (gu : g ≤ 1)
    (bill : ∀ j ≤ k, |nth j a| ≤ D) : |Lam.factor g k a| ≤ (k+1:ℝ)*D:=by
  refine (abs_sum_le_sum_abs (fun j=>g^j*nth j a) _).trans ((Finset.sum_le_sum (g:=fun _=>D) ?_).trans_eq (by simp))
  intro i hi
  rw [abs_mul, abs_of_nonneg (pow_nonneg gp _)]
  exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ gp gu)).trans (bill i (Nat.le_of_lt_succ (mem_range.mp hi)))

private def scale (k : ℕ) : ℝ := 1+3*((k+1:ℝ)+(2*(k+1:ℝ)+1)+(k+1:ℝ)^2)

private theorem forecast (k : ℕ) {d h : ℝ} (warm : 1 ≤ h) (pos : 0 ≤ d) (tariff : d ≤ 3*h) :
    d+Lam.pursed.forecastCost k d d ≤ scale k*h*d:=by
  let a:ℝ:=(k+1:ℝ)+(2*(k+1:ℝ)+1)+(k+1:ℝ)^2
  have az:0 ≤ a:=by dsimp [a];positivity
  have fee:1+a*d ≤ (1+3*a)*h:=by nlinarith only [warm, mul_le_mul_of_nonneg_left tariff az]
  calc
    d+Lam.pursed.forecastCost k d d = (1+a*d)*d:=by simp only [Lam.pursed.forecastCost,a];ring
    _ ≤ _:=mul_le_mul_of_nonneg_right fee pos

/-- The compact joint field and both means use the very same one-step Wilson law and the original inherited coupling. -/
def Receipt (e : Request G) (ε : ℝ) (b : ℕ) : Prop := ∀ (N p : ℕ), b+1 ≤ N →
  let S:=R.family.path.levels.clock.op b p
  ∀ (_T : Forest S.ratio), Bid.Larger (G:=G) S → ∀ (u : Directions G (R.family.side b p)),
  (∀i,‖u i‖ ≤ (e.2.2:ℝ)+1) → ∀ (x y : Unit→Site (R.family.side (b+1) p)) (H : ℕ),
  (2+log (β b))^3 ≤ (H:ℝ) → (∀i : Slice (first e),∀j : Slice (second e),
    H ≤ separation (legs (first e) x i).1 (legs (second e) y j).1) →
  let g:=regulatorRun R.family N p (b+1)
  |measured S u R (row e) (col e) (left e) (right e) x y g| ≤ ε*g^e.2.1

/-- The required Wick order and the true positive error radius are entered before every upper date and period. -/
theorem original (simple : G.Simple) (paid : Paid G R.kit) (e : Request G) (ε : ℝ) (positive : 0<ε) :
    ∀ᶠ b : ℕ in atTop, Receipt R e ε b:=by
  let q:=e.2.1
  let k:=q+4
  let high : Request G := (e.1,(k,e.2.2))
  let s:ℝ:=k+1
  have sp:0<s:=by dsimp [s];positivity
  let η:=ε/(2*s)
  have ep:0<η:=div_pos positive (by positivity)
  have amp:0 ≤ scale k:=by unfold scale;positivity
  have heat:=Station.hat_rate R.family.path.levels simple
  have tail:=WilsonMatrixTicketLanesReportedAccuracy.coupon R simple q 1 (scale k) (ε/2) amp (half_pos positive)
  filter_upwards [WilsonMatrixTicketLanesConnectedForecast.original R paid high,
    heat.eventually (WilsonMatrixTicketLanesRetainedSpatialRate.logarithms q η ep),heat.eventually_ge_atTop 4,
    RG01.Physical.nextHat simple R.family.path.levels, (tendsto_add_atTop_nat 1).eventually tail]
    with b sale spatial hot rise invoice N p live
  let S:=R.family.path.levels.clock.op b p
  intro _step T large u pinned x y H separated apart
  let g:=regulatorRun R.family N p (b+1)
  let D:=2+log (β b)
  have W:1 ≤ β b:=by linarith
  have hp:0<β b:=by linarith
  have Dp:0<D:=by dsimp [D];linarith only [log_nonneg W]
  have mono:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le b.le_succ
  have Wf : 1 ≤ β (b+1):=W.trans mono
  have Di:D ≤ 3*β (b+1):=by dsimp [D];linarith only [Real.log_le_self hp.le,mono,W]
  have ⟨_,gp,small⟩:=WilsonCoherentInheritedSpool.temperature R simple b N p live
  have gu:g ≤ 1:=small.trans (inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by linarith only [hot])))
  have reg:0<R.family.path.β N p (b+1):=Overlay.beta_positive R.makes.wilson live
  have upper: R.family.path.β N p (b+1) ≤ 2*β (b+1):=(R.makes.wilson.represents N p (b+1) live).band.2
  have low:(β b)⁻¹ ≤ g:=by
    apply inv_anti₀ (sqrt_pos.mpr reg)
    apply sqrt_le_iff.mpr
    exact ⟨hp.le,by nlinarith only [upper,rise,mul_nonneg hp.le (sub_nonneg.mpr hot)]⟩
  obtain ⟨P,X,_,width,forms⟩:=sale
  let net:=WilsonMatrixTicketLanesReflectedGauge.gap S T X u R (row e) (col e) (left e) (right e) x y
  obtain ⟨coeff,amount⟩:=forms p T large u (by simpa only [width] using pinned) x y
  have panel:=sum net k gp.le gu (coeff H apart)
  have signed : |Lam.factor g k net| ≤ ε/2*g^q:=by
    calc
      _ ≤ s*(D/exp (D⁻¹*(H:ℝ))):=panel
      _ ≤ s*(η*(β b)⁻¹^q):=mul_le_mul_of_nonneg_left (spatial H separated) sp.le
      _ ≤ s*(η*g^q):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hp.le) low q) ep.le) sp.le
      _ = _:=by dsimp only [η];field_simp [ne_of_gt sp]
  have rest : g^(k+1)*(D+Lam.pursed.forecastCost k D D) ≤ ε/2*g^q:=by
    calc
      _ ≤ g^(k+1)*(scale k*β (b+1)*D):=mul_le_mul_of_nonneg_left (forecast k Wf Dp.le Di) (pow_nonneg gp.le _)
      _ = scale k*β (b+1)^1*(g^(q+2*(1+1)+1)*D):=by dsimp only [k];rw [pow_one];ring
      _ ≤ _:=invoice b N p b.le_succ live
  have total:=add_le_add ((amount g gp small).trans rest) signed
  change |measured S u R (row e) (col e) (left e) (right e) x y g| ≤ ε*g^q
  let a:=measured S u R (row e) (col e) (left e) (right e) x y g
  have triangle : |a| ≤ |a-Lam.factor g k net|+|Lam.factor g k net|:=by simpa only [sub_zero] using abs_sub_le a (Lam.factor g k net) 0
  exact (triangle.trans total).trans_eq (by ring)

end YM.Integration.WilsonMatrixTicketLanesConnectedPositive
