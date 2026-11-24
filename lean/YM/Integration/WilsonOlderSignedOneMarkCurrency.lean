import YM.Integration.WilsonOlderSignedOneMarkPhysicalFare
import YM.Integration.WilsonMatrixOriginalStableInterval

/-! Restoring the scalar source wallet at one older date. A fixed loss of
four powers pays the regular recovery. Six grades pay the original hard
restamp before restoring the wallet. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkCurrency
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology

private def hardCost (q : ℕ) : ℝ := 2*Real.exp 102*(2:ℝ)^(q+1)

private theorem hard_pos (q : ℕ) : 0 < hardCost q := by unfold hardCost;positivity

def scale (q : ℕ) (ε : ℝ) : ℝ := min 1 (ε/(3*hardCost q*(2:ℝ)^q))

theorem positive (q : ℕ) {ε : ℝ} (ep : 0 < ε) : 0 < scale q ε := by
  exact lt_min one_pos (div_pos ep (mul_pos (mul_pos (by norm_num) (hard_pos q)) (by positivity)))

def opening {G : Gauge} (R : Run G) (simple : G.Simple) (q : ℕ) {ε : ℝ} (ep : 0 < ε) : ℕ :=
  (eventually_atTop.mp (IterationFour.Currency.g_small simple R.makes (scale q ε) (positive q ep))).choose

/-- The original two neighboring currencies satisfy these inequalities for every
cutoff and period above the same date. -/
theorem measured {G : Gauge} (R : Run G) (simple : G.Simple) {i m N per : ℕ} (hi : m ≤ i)
    (cut : i < N) (q : ℕ) {ε : ℝ} (ep : 0 < ε) (late : opening R simple q ep ≤ i) :
    let g:=regulatorRun R.family N per (i+1)
    let t:=regulatorRun R.family N per m
    0 < g ∧ 0 < t ∧ g ≤ 2*t ∧ g ≤ scale q ε := by
  obtain ⟨ht,localRate⟩:=WilsonMatrixOriginalStableInterval.local_coupling R simple m (i+1) N per
    (by omega) (by omega)
  exact ⟨IterationFour.Currency.g_pos R.makes N per (i+1) (by omega),ht,localRate,
    ((eventually_atTop.mp (IterationFour.Currency.g_small simple R.makes (scale q ε)
      (positive q ep))).choose_spec (i+1) (late.trans (Nat.le_succ i)) N per (by omega)).le⟩

theorem paid (q : ℕ) {g t ε δ u a b : ℝ} (hg : 0 < g) (ht : 0 < t)
    (hδ : 0 ≤ δ) (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b) (bound : g ≤ 2*t)
    (small : g ≤ scale q ε) (booked : (a+b)*δ*(2:ℝ)^q ≤ ε/3) :
    (a+b*(g⁻¹)^4)*(u+δ*g^(q+4))+2*Real.exp 102*(2*g^2)^(q+1)+(ε/3)*t^q  ≤ 
      (a+b)*(g⁻¹)^4*u+ε*t^q := by
  have one : g ≤ 1:=small.trans (min_le_left _ _)
  have tiny : g ≤ ε/(3*hardCost q*(2:ℝ)^q):=small.trans (min_le_right _ _)
  have big : (1:ℝ) ≤ (g⁻¹)^4:=one_le_pow₀ ((one_le_inv₀ hg).mpr one)
  have factor : a+b*(g⁻¹)^4 ≤ (a+b)*(g⁻¹)^4 := by
    rw [add_mul]; exact add_le_add (le_mul_of_one_le_right ha big) le_rfl
  have pot : g^q ≤ (2:ℝ)^q*t^q:=by rw [←mul_pow];exact pow_le_pow_left₀ hg.le bound q
  have split : (g⁻¹)^4*g^(q+4)=g^q := by
    rw [pow_add,inv_pow]; field_simp
  have fresh : (a+b)*(g⁻¹)^4*(δ*g^(q+4)) ≤ (ε/3)*t^q := by
    calc
      _ = (a+b)*δ*((g⁻¹)^4*g^(q+4)) := by ring
      _ = (a+b)*δ*g^q := by rw [split]
      _  ≤  (a+b)*δ*((2:ℝ)^q*t^q) := mul_le_mul_of_nonneg_left pot (mul_nonneg (add_nonneg ha hb) hδ)
      _ = ((a+b)*δ*(2:ℝ)^q)*t^q:=by ring
      _  ≤  _ := mul_le_mul_of_nonneg_right booked (pow_nonneg ht.le _)
  have high : g^(q+2) ≤ g:=by
    simpa using (pow_le_pow_of_le_one hg.le one (show 1 ≤ q+2 by omega))
  have limit := (le_div_iff₀ (mul_pos (mul_pos (by norm_num : 0 < (3:ℝ)) (hard_pos q))
    (by positivity : 0 < (2:ℝ)^q))).mp (high.trans tiny)
  have combined : hardCost q*g^(q+2)*(2:ℝ)^q ≤ ε/3 := by nlinarith only [limit]
  have hard : 2*Real.exp 102*(2*g^2)^(q+1) ≤ (ε/3)*t^q := by
    calc
      _ = hardCost q*(g^(q+2)*g^q) := by
        rw [mul_pow,←pow_mul,←pow_add,show 2*(q+1)=q+2+q by omega]
        unfold hardCost;ring
      _ = hardCost q*g^(q+2)*g^q:=by ring
      _  ≤  hardCost q*g^(q+2)*((2:ℝ)^q*t^q) :=
        mul_le_mul_of_nonneg_left pot (mul_nonneg (hard_pos q).le (pow_nonneg hg.le _))
      _ = (hardCost q*g^(q+2)*(2:ℝ)^q)*t^q:=by ring
      _  ≤  _ := mul_le_mul_of_nonneg_right combined (pow_nonneg ht.le _)
  have regular := mul_le_mul_of_nonneg_right factor (add_nonneg hu (mul_nonneg hδ (pow_nonneg hg.le (q+4))))
  rw [mul_add ((a+b)*(g⁻¹)^4)] at regular
  calc
    _  ≤  ((a+b)*(g⁻¹)^4*u+(ε/3)*t^q)+(ε/3)*t^q+(ε/3)*t^q :=
      add_le_add (add_le_add (regular.trans (add_le_add le_rfl fresh)) hard) le_rfl
    _ = (a+b)*(g⁻¹)^4*u+ε*t^q := by ring

end YM.Integration.WilsonOlderSignedOneMarkCurrency
