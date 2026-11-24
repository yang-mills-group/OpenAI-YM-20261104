import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Low frequencies in the fixed-box smooth remainder proof. The finite
sum retains every actual integer frequency, signed phase and ordered
shape derivative. Only the original fixed test loss enters the crop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalLowFourierJets
open Filter Finset
open scoped BigOperators

def cube (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N:ℤ)) N

def jet {d j : ℕ} (axis : Fin j → Fin d) (unit : Fin j → ℂ) (p : Fin d → ℤ) : ℂ :=
  ∏ i, unit i * (p (axis i) : ℂ)

private lemma count (d N : ℕ) : (cube d N).card = (2*N+1)^d := by
  rw [cube,Fintype.card_piFinset_const,Int.card_Icc]
  congr 1
  omega

private lemma price {d j N : ℕ} (axis : Fin j → Fin d) (unit : Fin j → ℂ)
    {p : Fin d → ℤ} (hp : p ∈ cube d N) : ‖jet axis unit p‖ ≤
      (∏ i, ‖unit i‖)*(N:ℝ)^j := by
  have member := Fintype.mem_piFinset.mp hp
  unfold jet
  rw [norm_prod]
  calc
    _ ≤ ∏ i, (‖unit i‖*(N:ℝ)) := Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => by
      have h := Finset.mem_Icc.1 (member (axis i))
      have hreal : |(p (axis i):ℝ)| ≤ N := by
        apply abs_le.mpr
        constructor
        · exact_mod_cast h.1
        · exact_mod_cast h.2
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using hreal
    _ = _ := by rw [Finset.prod_mul_distrib];simp

/-- Take N=floor(u⁻¹²). A crop chosen after the fixed seminorm, the number of
coordinates and the desired derivative pays the original integer Fourier sum. -/
theorem original {d j p loss Q : ℕ} (order : p+12*(d+j+loss) ≤ Q)
    (axis : Fin j → Fin d) (unit : Fin j → ℂ) (u A : ℝ) (hu : 0 < u) (hu1 : u ≤ 1)
    (hA : 0 ≤ A) (phase residual : (Fin d → ℤ) → ℂ)
    (modulus : ∀ v, ‖phase v‖ ≤ 1)
    (tested : ∀ v ∈ cube d ⌊(u⁻¹)^12⌋₊,
      ‖residual v‖ ≤ A*u^Q*(1+(⌊(u⁻¹)^12⌋₊:ℝ))^loss) :
    ‖∑ v ∈ cube d ⌊(u⁻¹)^12⌋₊, phase v * jet axis unit v * residual v‖ ≤
      3^d*2^loss*A*(∏ i, ‖unit i‖)*u^p := by
  let L := (u⁻¹)^12
  let N := ⌊L⌋₊
  let M := ∏ i, ‖unit i‖
  have hM : 0 ≤ M := prod_nonneg fun _ _ => norm_nonneg _
  have huI : 1 ≤ u⁻¹ := (one_le_inv₀ hu).2 hu1
  have hL : 1 ≤ L := one_le_pow₀ huI
  have hN : (N:ℝ) ≤ L := Nat.floor_le (zero_le_one.trans hL)
  have hcount : ((cube d N).card : ℝ) ≤ (3*L)^d := by
    rw [count];push_cast;gcongr;linarith
  have hpoly : (1+(N:ℝ))^loss ≤ (2*L)^loss :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have htested (v) (hv : v ∈ cube d N) : ‖phase v * jet axis unit v * residual v‖ ≤
      M*L^j*(A*u^Q*(2*L)^loss) := by
    rw [norm_mul,norm_mul]
    have hj : ‖jet axis unit v‖ ≤ M*L^j :=
      (price axis unit hv).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _) hM)
    have ht := (tested v hv).trans (mul_le_mul_of_nonneg_left hpoly (mul_nonneg hA (pow_nonneg hu.le _)))
    calc
      _ ≤ (1*(M*L^j))*(A*u^Q*(2*L)^loss) := by gcongr;exact modulus v
      _ = _ := by rw [one_mul]
  have hz : 0 ≤ M*L^j*(A*u^Q*(2*L)^loss) := by positivity
  have heat : L^(d+j+loss)*u^Q ≤ u^p := by
    change ((u⁻¹)^12)^(d+j+loss)*u^Q ≤ _
    rw [← pow_mul,inv_pow,inv_mul_eq_div,div_le_iff₀ (pow_pos hu _),← pow_add]
    exact pow_le_pow_of_le_one hu.le hu1 order
  calc
    _ ≤ ∑ v ∈ cube d N, ‖phase v * jet axis unit v * residual v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ cube d N, M*L^j*(A*u^Q*(2*L)^loss) := sum_le_sum htested
    _ = (cube d N).card*(M*L^j*(A*u^Q*(2*L)^loss)) := by simp
    _ ≤ (3*L)^d*(M*L^j*(A*u^Q*(2*L)^loss)) := mul_le_mul_of_nonneg_right hcount hz
    _ = (3^d*2^loss*A*M)*(L^(d+j+loss)*u^Q) := by rw [mul_pow,mul_pow,pow_add,pow_add];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left heat (by positivity)

end YM.Integration.WilsonOriginalLowFourierJets

