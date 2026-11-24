import YM.Integration.WilsonThermometerAncestralPrice
import YM.Integration.WilsonDyadicReportingPrice

/-! Pre-regulator change back to the physical source units following the common
close gallery. Its one geometric product covers the three radii and the old rent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralFunds
open Filter Finset Lattice Wilson RG RG16 QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped BigOperators Classical Topology

private def fee (q:ℕ):ℝ:=8*(1+3^(q+2))*3^(q+1)
private theorem fee₀ (q:ℕ) : 0 ≤ fee q := by unfold fee; positivity

private theorem restore {x y d m w:ℝ} (l:ℕ) (x0:0<x) (y0:0<y)
    (raise:y ≤ 3*x) (once:3^(l+1)*y ≤ 1) (d0:1 ≤ d) (loss:d^3 ≤ x⁻¹)
    (old:x^l ≤ m) (radius:w=m/d^3) : y^(l+2) ≤ w :=by
  have spare : y^(l+2) ≤ x^(l+1) := by
    calc y^(l+2) = y*y^(l+1) := by ring
         _ ≤ y*(3*x)^(l+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ y0.le raise _) y0.le
         _ = (3^(l+1)*y)*x^(l+1) := by rw [mul_pow];ring
         _ ≤ _ := mul_le_of_le_one_left (pow_nonneg x0.le _) once
  rw [radius,le_div_iff₀ (pow_pos (zero_lt_one.trans_le d0) _)]
  calc y^(l+2)*d^3 ≤ x^(l+1)*x⁻¹ := mul_le_mul spare loss (pow_nonneg (zero_le_one.trans d0) _) (pow_nonneg x0.le _)
       _ = x^l := by rw [pow_succ];field_simp
       _ ≤ m := old

private theorem rent {x y d Ω e r:ℝ} (s q:ℕ) (x0:0<x) (y0:0<y) (low:x ≤ 3*y)
    (d0:1 ≤ d) (o0:0 ≤ Ω) (r0:0 ≤ r) (income:e ≤ x^(q+2))
    (joint:d^3*Ω^s*r ≤ x⁻¹*(e+(3*x)^(q+2))) (small:fee q*y ≤ 1/4) :
    (8*Ω^s)*r ≤ (1/4)*y^q :=by
  have share : Ω^s*r ≤ d^3*Ω^s*r := by
    rw [mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg (pow_nonneg o0 _) r0) (one_le_pow₀ d0)
  have spend : x⁻¹*(e+(3*x)^(q+2)) ≤ (1+3^(q+2))*x^(q+1) := by
    calc _ ≤ x⁻¹*(x^(q+2)+(3*x)^(q+2)) :=
           mul_le_mul_of_nonneg_left (add_le_add_left income _) (inv_nonneg.mpr x0.le)
         _ = _ := by rw [mul_pow,show x^(q+2)=x^(q+1)*x by ring];field_simp
  calc (8*Ω^s)*r = 8*(Ω^s*r) := by ring
       _ ≤ 8*((1+3^(q+2))*x^(q+1)) := mul_le_mul_of_nonneg_left ((share.trans joint).trans spend) (by norm_num)
       _ ≤ 8*((1+3^(q+2))*(3*y)^(q+1)) := by gcongr
       _ = (fee q*y)*y^q := by unfold fee;rw [mul_pow];ring
       _ ≤ _ := mul_le_mul_of_nonneg_right small (pow_nonneg y0.le q)

variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "B" => budgetR R
include simple in
theorem original (degree a q l:ℕ) {Q:ℝ} (cap:0 ≤ Q) :
    ∀ᶠ i:ℕ in atTop,∀ t N per m:ℕ,m ≤ i → i+1 ≤ t → t<N → PaceR.Close R degree Q m t →
    let x:=regulatorRun R.family N per t
    let y:=regulatorRun R.family N per (i+1)
    ∀(d Ω e r mass w:ℝ) (s:ℕ),1 ≤ d → d ≤ ∏j∈Ico i t,(B j)^2*(B (j+1))^7 →
    0 ≤ Ω → Ω ≤ B i → s ≤ a → 0 ≤ e → e ≤ x^(q+2) → 0 ≤ r →
    r ≤ e+∑j∈Ico i t,(regulatorRun R.family N per (j+2))^(q+2) →
    (∀j∈Ico i t,2 ≤ B j) → x^l ≤ mass → w=mass/d^3 →
    (8*Ω^s)*r ≤ (1/4)*y^q ∧ y^(l+2) ≤ w := by
  have debit:=WilsonThermometerAncestralPrice.original R simple degree a (q+2) cap
    (η:=1) (by norm_num) (ε:=1) (by norm_num)
  have aperture:=WilsonThermometerAncestralPrice.original R simple degree a 0 cap
    (η:=1) (by norm_num) (ε:=0) (by norm_num)
  have forward:=WilsonReceivedCloseChainFunding.upper R simple degree Q
  have reverse:=WilsonReceivedCloseChainFunding.upper R simple 0 0
  have allow:=WilsonDyadicReportingPrice.reserve (C:=R.family) simple R.makes (fee q) 0 (1/4)
    (fee₀ q) (by norm_num)
  have extra:=WilsonDyadicReportingPrice.reserve (C:=R.family) simple R.makes ((3:ℝ)^(l+1)) 0 1
    (by positivity) (by norm_num)
  rcases eventually_atTop.mp (debit.and (aperture.and (forward.and (reverse.and (allow.and extra))))) with ⟨gate,ready⟩
  filter_upwards [eventually_ge_atTop gate] with i hi
  intro t N per m mi it top close x y d Ω e r mass w s one roof op page load e0 inc r0 sum stage priced wage
  obtain ⟨fiscal,ap,fw,_,_,_⟩:=ready t (by omega)
  obtain ⟨_,_,_,back,small,margin⟩:=ready (i+1) (by omega)
  have self : PaceR.Close R 0 0 (i+1) (i+1) := by simp [PaceR.Close]
  have bp:=back (i+1) le_rfl self N per (by omega) t it top.le
  have yp:=fw m (by omega) close N per top.le (i+1) (by omega) (by omega)
  have expense:=fiscal m (by omega) close N per top i mi (by omega)
    d Ω e r s (zero_le_one.trans one) roof op page load e0 stage (by simpa only [one_mul] using sum)
  have disk:=ap m (by omega) close N per top i mi (by omega)
    d 1 1 1 0 (zero_le_one.trans one) roof (by norm_num) (budget_pos R) (Nat.zero_le _) (by norm_num) stage (by simp)
  have fy : fee q*y ≤ 1/4 :=by simpa only [y,Real.rpow_zero,mul_one] using small per N (by omega)
  have gy : (3:ℝ)^(l+1)*y ≤ 1 :=by simpa only [y,Real.rpow_zero,mul_one] using margin per N (by omega)
  refine ⟨rent s q bp.1 yp.1 bp.2 one op r0 inc ?_ fy,restore l bp.1 yp.1 yp.2 gy one ?_ priced wage⟩
  · simpa only [Real.rpow_neg_one,one_mul] using expense
  · simpa only [pow_zero,mul_one,zero_mul,add_zero,Real.rpow_neg_one] using disk

end YM.Integration.WilsonThermometerAncestralFunds
