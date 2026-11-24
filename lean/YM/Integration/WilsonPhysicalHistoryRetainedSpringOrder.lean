import YM.Integration.WilsonPhysicalHistoryRetainedSpringCurvature
import YM.Integration.WilsonPhysicalHistoryRetainedSpringIncoming

/-! The inverse physical temperature, the measured kinetic reset and every
curvature slot of an occupied filed row are valued on the same configuration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice Wilson RG Precision IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped BigOperators Classical
variable {G : Gauge} {n : Side}

theorem occupied_order (a : PrismA G) {σ C : ℝ} (hs : 0<σ)
    (paid : Commission a.cells σ C a.grade) (x : Site n) (U : Config G n)
    {g p M : ℝ} (hg : 0<g) (lo : 1/2≤p) (hi : p≤3/2) (hM : 0≤M)
    (tips : ∀ s : Signed,∀ i : ℕ,∀ l : Fin (a.rise+2),
      tip ((a.cells i).leg l) (pull s 0 U) x≤g*M) :
    |Integral.temperature g*p*(g/Real.sqrt p)^(a.grade-a.rise)*sitePacket a.cells x U|≤
      2^(a.grade-a.rise+1)*C*M^(a.rise+2)*g^a.grade := by
  have hp : 0<p := by linarith
  have sq := Real.sq_sqrt hp.le
  have hsqrt : (1/2:ℝ)≤Real.sqrt p := by nlinarith [Real.sqrt_nonneg p]
  have hc : |g/Real.sqrt p|≤2*g := by
    rw [abs_of_nonneg (div_nonneg hg.le (Real.sqrt_nonneg _)),div_le_iff₀ (Real.sqrt_pos.2 hp)]
    nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hsqrt)]
  have hb : |Integral.temperature g*p|≤(g^2)⁻¹*2 := by
    unfold Integral.temperature
    rw [abs_of_nonneg (mul_nonneg (by positivity) hp.le)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have term:=site_tips a.cells hs paid.toll x U (mul_nonneg hg.le hM) tips
  have expn : a.grade-a.rise+(a.rise+2)=a.grade+2 := by have :=a.rankA; omega
  have powers : g^(a.grade-a.rise)*g^(a.rise+2)=g^a.grade*g^2 := by
    rw [←pow_add,←pow_add,expn]
  calc
    _ ≤ (g^2)⁻¹*2*(2*g)^(a.grade-a.rise)*(C*(g*M)^(a.rise+2)) := by
      rw [abs_mul,abs_mul,abs_pow]
      exact mul_le_mul (mul_le_mul hb (pow_le_pow_left₀ (abs_nonneg _) hc _)
        (by positivity) (by positivity)) term (abs_nonneg _) (by positivity)
    _ = (g^2)⁻¹*(g^(a.grade-a.rise)*g^(a.rise+2))*
        (2^(a.grade-a.rise+1)*C*M^(a.rise+2)) := by rw [mul_pow,mul_pow,pow_succ (2:ℝ)]; ring
    _ = _ := by rw [powers]; field_simp [hg.ne']

end YM.Integration.OriginalMarkedRunAction
