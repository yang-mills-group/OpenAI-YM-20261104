import YM.Pert.Triangle.ScalarFan
import YM.Pert.Triangle.Operators
/-! Fan polarization on actual degree-zero shell legs. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Pert.Triangle
open Maxwell UVNext.FreeStress Function Labels
open scoped Topology Classical
local notation "I"=>Fin 3
variable {G : Gauge}
variable (h : Bool) (i : I) (u : G.ColorIndex)

def probe := (2:ℝ)⁻¹ • ∑ a,∑ b, fan h i a b • curlProbe (G:=G) (initialPlace a b) u
def lineReader : Labels.Taylor G 0 →ₗ[ℝ] ℝ := (PiLp.projₗ 2 (fun _:G.ColorIndex=>ℝ) u) ∘ₗ (fanReading h i)
lemma probe_eq : probe h i u = lineReader h i u ∘ₗ gaugeJet := by
  ext1 s
  simp_rw [lineReader,fanReading,probe]; simp only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.sum_apply,PiLp.projₗ_apply,PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,smul_eq_mul]
  congr 1; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
  unfold component; dsimp; rw [match_leg];rfl
lemma reduced_fan : reduceEq (fanLeg h i u) = symbol 0 (probe h i u) := by
  refine equalPol _ _ fun A=>?_; rw [Maxwell.jet_value, Maxwell.symbol_test,read_fan,probe_eq];rfl
private theorem curl_rates {z : E4} (hz : z≠0) (a b c d : Axis) (i j : G.ColorIndex) : pairing (show z∈away from hz) (curlProbe ((initialPlace a b)) i) (curlProbe (initialPlace c d) j)= if i=j then bareCurl a b c d z else 0 := by
  unfold curlProbe; rw [Maxwell.raw_mixed _ _ _ _ _ _ _ _ hz]; simp only [Tensor.coeff_apply_zero,pow_zero,one_mul]
variable (k v) {z : E4}
lemma probe_pair (hz : z≠0) : legKernel (probe h i u) (probe h k v) z = (2:ℝ)⁻¹ * (2:ℝ)⁻¹ * (∑ a,∑b, fan h i a b * (∑ c,∑ d,fan h k c d * (if u=v then bareCurl a b c d z else 0))) := by
  let p := Maxwell.pairing (show z∈away from hz) (G:=G) (j:=0) (l:=0)
  change p _ _ = _
  unfold probe; rw [map_smul,map_sum]; simp_rw [map_smul,map_sum]; simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,smul_eq_mul,p,curl_rates hz]
  rw [mul_assoc]; simp_rw [Finset.mul_sum]
  -- swap outer sums twice
  let F (a b c d:Axis):=(2:ℝ)⁻¹*(2:ℝ)⁻¹*(fan h k c d * (fan h i a b * if u=v then bareCurl a b c d z else 0))
  change (∑ a,∑ b,∑ c,∑ d, _)=_
  calc
    _ = ∑ c,∑ d,∑a,∑b,F a b c d := by unfold F; exact Finset.sum_congr rfl (fun c _=>Finset.sum_congr rfl fun d _=>Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=>by ring)
    _ = ∑ a,∑ b,∑ c,∑ d,F a b c d := by
      exact Eq.trans (by simpa only [Fintype.sum_prod_type,uncurry] using Finset.sum_comm (f:=fun x y : (Axis × Axis) => F y.1 y.2 x.1 x.2) (s:=Finset.univ) (t:=Finset.univ) ) rfl -- argument names
    _ = _ := by unfold F; exact Finset.sum_congr rfl (fun a _=>Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun c _=> Finset.sum_congr rfl fun d _=> by ring)
lemma fan_kernel (hz : z≠0) : legKernel (probe h i u) (probe h k v) z = 0 := by rw [probe_pair _ _ _ _ _ hz]; by_cases H:u=v <;> simp [H,green_antiself h i k hz]
end YM.Pert.Triangle
