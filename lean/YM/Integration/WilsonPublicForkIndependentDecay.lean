import YM.Integration.WilsonPublicForkCoefficientIntegral
import YM.Integration.WilsonPublicForkSeriesProduct

/-! Estimates for the evaluated independent scalar on its actual finite
Taylor rectangle, with the measuring variable exp(-τs) at log separation s. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIndependentDecay
open Filter Function Finset Set PowerSeries FVA2 FVA2.O FVA2.O.Score FVA2.O.Enh
open MS MS.LogTime WilsonMSDictionaryFarRead WilsonPublicForkSeriesProduct
open scoped Classical Topology BigOperators
variable {I:Type}

def measuring (τ s:ℝ):ℝ:=Real.exp (-τ*s)

theorem power (τ:ℝ)(k:ℕ):
    Rain (τ*(k:ℝ)) (fun (_:I) s=>(measuring τ s:ℂ)^k):=by
  have eq:(fun (_:I) s=>(measuring τ s:ℂ)^k)=(fun (_:I) s=>fee s (τ*(k:ℝ))):=by
    funext i s
    unfold measuring fee
    rw [←Complex.ofReal_pow,←Real.exp_nat_mul]
    apply congrArg Complex.ofReal
    apply congrArg Real.exp
    ring
  rw [eq];exact Rain.all_fee

theorem evaluation {a:ℝ}{F:I→ℝ→PowerSeries ℂ}(q:ℕ)(τ:ℝ)(lp:0≤τ)(billed:ChargeP (q+1) a F):
    Rain a (fun i s=>cutoff q (measuring τ s) (F i s)):=by
  unfold cutoff
  apply Rain.sum
  intro k bound
  exact ((power (I:=I) τ k).mul (billed k (mem_range.mp bound))).size
    (by have:=mul_nonneg lp (Nat.cast_nonneg (α:=ℝ) k);linarith)

theorem overshoot {a:ℝ}{F B:I→ℝ→PowerSeries ℂ}(q:ℕ)(τ:ℝ)(lp:0≤τ)
    (front:ChargeP (q+1) 0 F)(far:ChargeP (q+1) a B):
    Rain (a+τ*(q+1)) (fun i s=>cutoff q (measuring τ s) (F i s)*cutoff q (measuring τ s) (B i s)-
      cutoff q (measuring τ s) (F i s*B i s)):=by
  simp only [square]
  apply Rain.sum
  intro p pos
  obtain ⟨p₀,p₁⟩:=mem_product.mp (mem_filter.mp pos).1
  have shared:((q:ℝ)+1)≤(p.1+p.2:ℕ):=by exact_mod_cast late pos
  apply (((power (I:=I) τ (p.1+p.2)).mul (front p.1 (mem_range.mp p₀))).mul (far p.2 (mem_range.mp p₁))).size
  have:=mul_le_mul_of_nonneg_left shared lp
  linarith

theorem pays {a b:ℝ}{f:I→ℝ→ℂ}(H:Rain a f)(margin:b<a):
    ∀ᶠ s in atTop,∀i,‖f i s‖≤Real.exp (-b*s):=by
  obtain ⟨C,cp,k,paid⟩:=H
  have small:Tendsto (fun s=>C*LogTime.polyExp (a-b) k s) atTop (𝓝 0):=by
    simpa using tendsto_const_nhds.mul (LogTime.vanishes (sub_pos.mpr margin) k)
  filter_upwards [paid,small.eventually (ge_mem_nhds zero_lt_one)] with s w cap i
  have eq:Real.exp (-a*s)=Real.exp (-(a-b)*s)*Real.exp (-b*s):=by rw [←Real.exp_add];congr 1;ring
  calc
    _ ≤ C*post a s k:=w i
    _ = (C*LogTime.polyExp (a-b) k s)*Real.exp (-b*s):=by unfold post LogTime.polyExp;rw [eq];ring
    _ ≤ Real.exp (-b*s):=mul_le_of_le_one_left (Real.exp_pos _).le cap

end YM.Integration.WilsonPublicForkIndependentDecay
