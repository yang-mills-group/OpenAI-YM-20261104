import YM.Integration.WilsonTrueProjectedPhysicalProgram
import YM.Integration.WilsonTrueProjectedUVBoundary

/-! A grade-wise original column sale in the natural units of the receiving
field pays the dated signed forcing. The fine-to-coarse engineering factor is
one block. All cutoff dependence in the submitted vector remains explicit. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedNaturalFee
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FormalBulk08 City Pose Push ConnectedActivityE6 PhysicalNext Repeat Legato Graces Roost Org
open WilsonTrueProjectedDatedProgram WilsonTrueProjectedCourse
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
local notation "𝓒" => R.family
local notation "V" => R.family.path.levels

theorem physical (m i q : ℕ) {g B stretch : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B)
    (x : Fin (q+1) → ι → ℂ) (A : Fin (q+1) → ℝ) (u v : Fin (q+1) → ι → ℝ)
    (wage : ∀ k, mesh R d m (i+1)*(∑ b, ‖x k b‖) ≤ A k*stretch*g^k.val)
    (sale : ∀ k b, u k b+v k b ≤ B*g^(q-k.val+1)) :
    mesh R d m i * (∑ k : Fin (q+1), ∑ b, ‖x k b‖*(u k b+v k b)) ≤
      (((𝓒).S.block i).val:ℝ)^d*((∑ k,A k)*B)*g^(q+1)*stretch := by
  let L : ℝ := ((𝓒).S.block i).val
  have pos : 0 < L := by dsimp only [L]; exact_mod_cast ((𝓒).S.block i).pos
  have factor : mesh R d m i = L^d*mesh R d m (i+1) := by
    rw [next_mesh]
    change _ = L^d*(_/L^d)
    field_simp
  have nonneg : 0 ≤ mesh R d m (i+1) :=
    pow_nonneg (div_nonneg ((𝓒).S.a_pos _).le ((𝓒).S.a_pos _).le) _
  have realNorm : ‖(mesh R d m (i+1) : ℂ)‖ = mesh R d m (i+1) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg nonneg]
  let y (k : Fin (q+1)) (b : ι) := (mesh R d m (i+1) : ℂ) * x k b
  have bound := grade_price R hg hB y (fun k => A k*stretch) u v (fun k => by
    simpa only [y,norm_mul,realNorm,Finset.mul_sum] using wage k) sale
  calc
    _ = L^d*(∑ k : Fin (q+1), ∑ b, ‖y k b‖*(u k b+v k b)) := by
      rw [factor,mul_assoc]
      congr 1
      simp only [y,norm_mul,realNorm,Finset.mul_sum,mul_assoc]
    _ ≤ _ := (mul_le_mul_of_nonneg_left bound (pow_nonneg pos.le d)).trans_eq (by
      rw [←Finset.sum_mul]
      dsimp only [L]
      ring)

private theorem hat_power {H : ℝ} (hH : 0 < H) (n : ℕ) :
    Coat.gStep H^n = H^(-(n:ℝ)/2) := by
  change (Real.sqrt H)⁻¹^n = _
  rw [inv_pow,Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hH.le,←Real.rpow_neg hH.le]
  congr 1
  ring

private theorem compare {H β : ℝ} (hH : 0 < H) (band : H/2 ≤ β) :
    Coat.gStep β ≤ 2*Coat.gStep H := by
  have hb : 0 < β := (half_pos hH).trans_le band
  have order := Real.sqrt_le_sqrt (show H ≤ 4*β by linarith)
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4 = 2 by norm_num] at order
  change (Real.sqrt β)⁻¹ ≤ 2*(Real.sqrt H)⁻¹
  have hx := Real.sqrt_pos.mpr hH
  have hy := Real.sqrt_pos.mpr hb
  rw [inv_eq_one_div,inv_eq_one_div,←mul_div_assoc]
  rw [div_le_div_iff₀ hy hx]
  linarith

/-- The original temperature band and its actual funded column salary absorb
the single block factor before either regulator is chosen. -/
theorem calendar (simple : G.Simple)
    (slow : ∀ j, (((𝓒).S.block j).val:ℝ) ≤ Real.log (RG16.Lambda (V) j))
    (d q target : ℕ) (enough : target + 2*(d+1) ≤ q+1) :
    ∀ᶠ i : ℕ in atTop, ∀ N p : ℕ, i ≤ N →
      let g := Coat.gStep ((𝓒).path.rep N p i).beta
      0 < g ∧ (2+4*stock (𝓒) i)*(((𝓒).S.block i).val:ℝ)^d*g^(q+1) ≤
        (10*3^d*2^(q+1))*power R target i := by
  obtain ⟨start,cols⟩ := eventually_atTop.mp (WilsonRegisteredLogFare.column R simple slow)
  filter_upwards [Filter.eventually_ge_atTop (start+1)] with i late
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i≠0 by omega)
  intro N p live
  let H := (V).clock.hatBeta (j+1)
  let β := ((𝓒).path.rep N p (j+1)).beta
  have h1 : 1 < H := (V).fits.delayed _
  have hH : 0 < H := zero_lt_one.trans h1
  have band : H/2 ≤ β := (R.makes.wilson.represents N p _ live).band.1
  have hg : 0 < Coat.gStep β := inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos hH).trans_le band))
  refine ⟨hg,?_⟩
  have column : stock (𝓒) (j+1) ≤ 2*H := (cols j (by omega)).trans
    (mul_le_mul_of_nonneg_left (Real.log_le_self hH.le) (by norm_num))
  have facility : (2+4*stock (𝓒) (j+1)) ≤ 10*H := by linarith
  have width : (((𝓒).S.block (j+1)).val:ℝ) ≤ 3*H := by
    apply (slow (j+1)).trans
    change Real.log (2+Real.log H) ≤ _
    have lo := Real.log_nonneg h1.le
    exact (Real.log_le_self (by linarith)).trans (by linarith [Real.log_le_self hH.le])
  have powers : (H^(d+1)) * H^(-((q+1:ℕ):ℝ)/2) ≤ H^(-(target:ℝ)/2) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hH]
    apply Real.rpow_le_rpow_of_exponent_le h1.le
    have order : (target:ℝ) + 2*((d:ℝ)+1) ≤ (q:ℝ)+1 := by exact_mod_cast enough
    push_cast
    linarith
  change (2+4*stock (𝓒) (j+1))*_*Coat.gStep β^(q+1) ≤ _
  have geom := pow_le_pow_left₀ (Nat.cast_nonneg _) width d
  have coupl := pow_le_pow_left₀ hg.le (compare hH band) (q+1)
  calc
    _ ≤ (10*H)*(3*H)^d*(2*Coat.gStep H)^(q+1) :=
      mul_le_mul (mul_le_mul facility geom (by positivity) (by positivity)) coupl (by positivity) (by positivity)
    _ = (10*3^d*2^(q+1))*(H^(d+1)*H^(-((q+1:ℕ):ℝ)/2)) := by
      rw [mul_pow,mul_pow,hat_power hH,pow_succ]
      ring
    _ ≤ _ := by
      unfold power
      rw [max_eq_right h1.le]
      exact mul_le_mul_of_nonneg_left powers (by positivity)

end YM.Integration.WilsonTrueProjectedNaturalFee
