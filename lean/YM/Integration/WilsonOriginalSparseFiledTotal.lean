import YM.Integration.WilsonOriginalSparseFiledJointSale

/-! A fixed angular horizon spends one power of the physical clock on all cropped
coordinate tuples, the radial extraction constants and the finite sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledTotal
open Filter Finset Stationary Push.AbsoluteSums.Animals
open WilsonOriginalSparseFiledNodalSale (seatsCost)
open WilsonOriginalSparseFiledNodes (factor)
open scoped Classical Topology BigOperators

def crop (H:ℝ) : ℕ := Nat.ceil ((Real.log H)^2)/32

def load (G:Gauge) (d:ℕ) (H:ℝ) : ℝ :=
  (d.factorial:ℝ)*∑r∈range (d+1), (seatsCost G (crop H) r*factor d + 2)

private def localCost (G:Gauge) : ℝ := 1+5^4*(Fintype.card (Loc G 1):ℝ)

private theorem seat (G:Gauge) {H:ℝ} (log1:1≤Real.log H) {r d:ℕ} (hr:r≤d) :
    seatsCost G (crop H) r ≤ localCost G^d*(Real.log H)^(8*d) := by
  let t:=Real.log H
  have t1:1≤t:=log1
  have t0:0≤t:=zero_le_one.trans t1
  have tw:1≤t^2:=one_le_pow₀ t1
  have rounded:(crop H:ℝ)≤t^2+1:=by
    refine le_trans ?_ (Nat.ceil_lt_add_one (sq_nonneg t)).le
    change ((Nat.ceil (t^2)/32:ℕ):ℝ) ≤ (Nat.ceil (t^2):ℝ)
    exact Nat.cast_le.mpr (Nat.div_le_self _ _)
  have side:(crop H:ℝ)+(crop H:ℝ)+1≤5*t^2:=by linarith
  have base:1≤localCost G*t^8:=one_le_mul_of_one_le_of_one_le (by unfold localCost;exact le_add_of_nonneg_right (by positivity)) (one_le_pow₀ t1)
  have bound:((ballCost (crop H)*Fintype.card (Loc G 1):ℕ):ℝ) ≤ localCost G*t^8:=by
    simp only [ballCost,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ (5*t^2)^4*(Fintype.card (Loc G 1):ℝ):=by gcongr
      _ ≤ localCost G*t^8:=by unfold localCost; nlinarith only [pow_nonneg t0 8]
  calc
    _ ≤ (localCost G*t^8)^r:=by unfold seatsCost; gcongr
    _ ≤ (localCost G*t^8)^d:=pow_le_pow_right₀ base hr
    _ = _:=by rw [mul_pow,←pow_mul]

private def fixedCost (G:Gauge) (d:ℕ):ℝ :=
  (d.factorial:ℝ)*(d+1)*(localCost G^d*factor d+2)

private theorem poly (G:Gauge) (d:ℕ) {H:ℝ} (log1:1≤Real.log H) :
    load G d H≤fixedCost G d*(Real.log H)^(8*d) := by
  have one:1≤(Real.log H)^(8*d):=one_le_pow₀ log1
  have fac:0≤factor d:=zero_le_one.trans (le_max_left ..)
  let t:=(Real.log H)^(8*d)
  calc
    _ ≤ (d.factorial:ℝ)*∑ _r∈range (d+1),((localCost G^d*factor d+2)*t):=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); apply sum_le_sum
      intro r hr
      have sell:=mul_le_mul_of_nonneg_right (seat G log1 (Nat.lt_succ_iff.mp (mem_range.mp hr))) fac
      dsimp only [t];nlinarith only [sell,one]
    _ = _:=by simp [fixedCost,t]; ring

/-- The opening is chosen for the finite horizon, without choosing a torus, a
marked source, a late cutoff, or an angular derivative point. -/
theorem calendar (G:Gauge) (cap:ℕ) : ∀ᶠ H:ℝ in atTop, 1≤H ∧ ∀d≤cap,load G d H≤H := by
  have each (d:ℕ):∀ᶠ H:ℝ in atTop,load G d H≤H:=by
    let C:=max 1 (fixedCost G d)
    have cp:0<C:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
    have s:=(isLittleO_log_rpow_rpow_atTop ((8*d:ℕ):ℝ) (show (0:ℝ)<1 by norm_num)).def (inv_pos.mpr cp)
    filter_upwards [s,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with H hs log1 h1
    have l0:0≤Real.log H:=zero_le_one.trans log1
    have hb:(Real.log H)^(8*d)≤C⁻¹*H:=by
      simpa only [Real.rpow_natCast,Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg l0 _),
        abs_of_nonneg (zero_le_one.trans h1)] using hs
    calc
      _ ≤ fixedCost G d*(Real.log H)^(8*d):=poly G d log1
      _ ≤ C*(Real.log H)^(8*d):=mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg l0 _)
      _ ≤ C*(C⁻¹*H):=mul_le_mul_of_nonneg_left hb cp.le
      _=H:=by rw [←mul_assoc,mul_inv_cancel₀ cp.ne',one_mul]
  filter_upwards [eventually_ge_atTop (1:ℝ), (Finset.eventually_all (range (cap+1))).mpr
    (fun d _=>each d)] with H h1 every
  exact ⟨h1,fun d hd=>every d (mem_range.mpr (Nat.lt_succ_of_le hd))⟩

/-- Includes the true scalar and the two distinct upper/lower off-hull allowances.
The winding price is multiplied by this same finite dated charge. -/
theorem total (G:Gauge) {H ω:ℝ} (h1:1≤H) (hω:0≤ω) (m pole height P saved:ℕ)
    (cut:m=crop H) (stock:∀d≤3*height,load G d H≤H) (enough:P+1≤ saved)
    (fee:ℕ→ℕ→ℝ) (paid:∀e,e+pole<3*height →∀r≤e+pole,fee e r≤(H^(P+1))⁻¹+ω) :
    ∀e,e+pole<3*height → ((e+pole).factorial:ℝ)*
      (∑r∈range (e+pole+1),(seatsCost G m r*(factor (e+pole)*fee e r)+2*(H^saved)⁻¹))
        ≤ (H^P)⁻¹+H*ω := by
  intro e live
  subst m
  let d:=e+pole
  let cash:=(H^(P+1))⁻¹+ω
  have hp:0<H:=zero_lt_one.trans_le h1
  have quiet:(H^saved)⁻¹≤cash:=by
    exact (inv_anti₀ (pow_pos hp _) (pow_le_pow_right₀ h1 enough)).trans (le_add_of_nonneg_right hω)
  have non:0≤cash:=by dsimp [cash];positivity
  calc
    _ ≤ (d.factorial:ℝ)*∑r∈range (d+1),(seatsCost G (crop H) r*factor d+2)*cash:=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _);apply sum_le_sum
      intro r hr
      have a:0≤ seatsCost G (crop H) r:=by unfold seatsCost; positivity
      have f:0≤factor d:=zero_le_one.trans (le_max_left ..)
      have sub:=mul_le_mul_of_nonneg_left (paid e live r (Nat.lt_succ_iff.mp (mem_range.mp hr))) (mul_nonneg a f)
      dsimp only [d] at *
      nlinarith only [sub,quiet]
    _ = load G d H*cash:=by rw [load,←Finset.sum_mul, mul_assoc]
    _ ≤ H*cash:=mul_le_mul_of_nonneg_right (stock d live.le) non
    _ = _:=by dsimp [cash];rw [mul_add,pow_succ];field_simp

end YM.Integration.WilsonOriginalSparseFiledTotal
