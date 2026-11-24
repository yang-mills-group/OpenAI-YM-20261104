import YM.Integration.WilsonMatrixTicketLanesRetainedDecayBudget
import YM.Integration.WilsonMatrixTicketLanesRetainedQuadraticChamber

/-! The actual separated quadratic primary costs every requested power on the original measured clock. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedSpatialRate
open Function Filter Set Real Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Silk Next.Rank RG12
open RGComparison.Core16.Parcel FVA2.CityHistory WilsonMatrixTicketLanesRetainedQuadraticChamber
open WilsonMatrixTicketLanesRetainedAngular WilsonMatrixTicketLanesRetainedCrossed WilsonMatrixTicketLanesRetainedCurls
open WilsonMatrixTicketLanesReflectedInner Pert.Asymptotics
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)
local notation "β" => R.family.path.levels.clock.hatBeta

/-- The paid decay envelope involves only the original stage's own temperature. -/
theorem priced (paid : WilsonMatrixTicketLanesRetainedDecayBudget.Paid G R.kit) (cap : ℕ) :
    ∀ᶠ b : ℕ in atTop,Bound R b cap (2+log (β b))⁻¹ (2+log (β b)) := by
  filter_upwards [paid cap] with b sale
  obtain ⟨P,X,C,offer,width,c₀,front,rate,receipt⟩:=sale
  have backward : (2+log (β b))⁻¹ ≤ shade X:=(inv_anti₀ (inv_pos.mpr shade_pos) rate).trans_eq (inv_inv _)
  intro p S T large tag nil u seated a a' c c' i j k l H far
  have field:=fromOffer R b cap X offer width c₀ receipt p T large tag nil u seated a a' c c' i j k l H far
  exact field.trans (div_le_div₀ ((mul_nonneg (by norm_num) c₀).trans front) front (exp_pos _) (exp_monotone
    (mul_le_mul_of_nonneg_right backward (Nat.cast_nonneg _))))

theorem logarithms (q : ℕ) (ε : ℝ) (pos : 0<ε) : ∀ᶠ x : ℝ in atTop,
    ∀ h : ℝ,(2+log x)^3≤h → (2+log x)/exp ((2+log x)⁻¹*h)≤ε*(x⁻¹)^q := by
  have grows:=tendsto_atTop_add_const_left _ (2:ℝ) tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (max 2 ε⁻¹),grows.eventually_ge_atTop ((q:ℝ)+2)] with x above ahead h far
  let D:=2+log x
  have x₀:0<x:=lt_of_lt_of_le (by norm_num) ((le_max_left ..).trans above)
  have positive : 0<D:=lt_of_lt_of_le (by positivity : (0:ℝ)<(q:ℝ)+2) ahead
  have fee : ((q+1:ℕ):ℝ)*D+D≤D⁻¹*h:=by
    rw [←div_eq_inv_mul]
    apply (le_div_iff₀ positive).2
    calc
      (((q+1:ℕ):ℝ)*D+D)*D=((q:ℝ)+2)*(D*D):=by push_cast;ring
      _ ≤ D*(D*D):=mul_le_mul_of_nonneg_right ahead (mul_nonneg positive.le positive.le)
      _ ≤ h:=by simpa [pow_succ,mul_assoc] using far
  have expHigh : x≤exp D:=by rw [←exp_log x₀];exact exp_monotone (by dsimp [D];linarith)
  have scale : x⁻¹≤ε:=(inv_anti₀ (inv_pos.mpr pos) ((le_max_right ..).trans above)).trans_eq (inv_inv _)
  change D/exp (D⁻¹*h) ≤ _
  calc
    D/exp (D⁻¹*h) ≤ exp D/exp (((q+1:ℕ):ℝ)*D+D):=
      div_le_div₀ (exp_pos _).le (by linarith only [add_one_le_exp D]) (exp_pos _) (exp_monotone fee)
    _=((exp D)⁻¹)^(q+1):=by rw [exp_add ((q+1:ℕ)*D) D,exp_nat_mul,inv_pow];field_simp
    _≤(x⁻¹)^(q+1):=pow_le_pow_left₀ (inv_nonneg.mpr (exp_pos _).le) (inv_anti₀ x₀ expHigh) _
    _≤ε*(x⁻¹)^q:=by rw [pow_succ,mul_comm ε];exact mul_le_mul_of_nonneg_left scale (pow_nonneg (inv_nonneg.mpr x₀.le) _)

/-- At a separation of three powers of the original logarithmic scale, every finite period
and every upper regulator share the requested power of the true positive running coupling. -/
theorem purchased (simple : G.Simple) (paid : WilsonMatrixTicketLanesRetainedDecayBudget.Paid G R.kit)
    (cap q : ℕ) (ε : ℝ) (pos : 0<ε) : ∀ᶠ b : ℕ in atTop,∀p : ℕ,
    let S:=R.family.path.levels.clock.op b p
    ∀ (T : Forest S.ratio) (large : Bid.Larger (G:=G) S) (tag : S.Choices)
      (nil : (Descent.nil (top:=R.family.side (b+1) p)).Tags) (u : Directions G (R.family.side b p)),
      (∀e,‖u e‖≤(cap:ℝ)+1) → ∀ (z₀ z₁ z₂ z₃ : Face (Per (R.family.side (b+1) p)))
      (i j k l : G.ColorIndex) (H : ℕ),WilsonMatrixTicketLanesRetainedQuadraticWalls.clear z₀ z₁ z₂ z₃ H →
      (2+log (β b))^3≤(H:ℝ) → ∀ N,b≤N →
      |cross (law S T large tag nil) (curl S T z₀ i) (curl S T z₁ j) (curl S T z₂ k) (curl S T z₃ l)
        (changeField S T large tag nil u)| ≤ ε*(regulatorRun R.family N p b)^q := by
  have heat:=Station.hat_rate R.family.path.levels simple
  filter_upwards [priced R paid cap,heat.eventually (logarithms q ε pos),heat.eventually_ge_atTop 2]
    with b bill pay hot p S T large tag nil u seated z₀ z₁ z₂ z₃ i j k l H far gap N future
  have warm:0<β b:=lt_of_lt_of_le (by norm_num) hot
  have band:= (R.makes.wilson.represents N p b future).band.2
  change R.family.path.β N p b≤2*β b at band
  have small: sqrt (R.family.path.β N p b)≤β b:=by
    apply Real.sqrt_le_iff.mpr
    exact ⟨warm.le,band.trans (by nlinarith only [mul_nonneg warm.le (sub_nonneg.mpr hot)])⟩
  have bp : 0<R.family.path.β N p b:=Overlay.beta_positive R.makes.wilson future
  have trueCoupling : (β b)⁻¹≤regulatorRun R.family N p b:=inv_anti₀ (sqrt_pos.mpr bp) small
  exact (bill p T large tag nil u seated z₀ z₁ z₂ z₃ i j k l H far).trans ((pay H gap).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr warm.le) trueCoupling _) pos.le))

end YM.Integration.WilsonMatrixTicketLanesRetainedSpatialRate
