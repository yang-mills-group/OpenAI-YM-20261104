import YM.Integration.WilsonPositionProgramAngularDirection
import YM.Integration.WilsonPositionProgramCurvedQuietSlot

/-! The full curved jet uses one order-dependent price on the centered formal inputs at their true thermal scale. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramCurvedAngularPrice
open Function Finset Lattice Tree RG Work.F03 WilsonPositionProgramAngularChart
open WilsonPositionProgramThermalPolar WilsonPositionProgramAngularDirection Comparison.RG02
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {c f:Side}{g:Ratio c f}

def price (G:Gauge)(k v:ℕ):ℝ:=
  (k.factorial:ℝ)⁻¹ * ∑p:OrderedFinpartition k,
    let w:=weights (fun i=>clock (p.partSize i))
    ∑u∈w.support,|w u| * (p.length.factorial:ℝ) * (1+mass G p.partSize u)^v

private theorem sums {I:Type*}(Q:Finset I)(v a:I→ℝ)(M:ℝ)
    (h:∀i∈Q,|v i|≤a i*M): |∑i∈Q,v i|≤(∑i∈Q,a i)*M:=by
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by rw [Finset.sum_mul]; exact Finset.sum_le_sum h)

private theorem landed (F:Forest g)(k:ℕ)(p:OrderedFinpartition k)(b b₀:ChartVars F G)
    (u:Slots p.length):
    let x:=fun q:ChartVars F G=>angular (fun i=>part (axisLog F) (p.partSize i) q) u
    1+max ‖x b‖ ‖x b₀‖≤(1+mass G p.partSize u)*(1+max ‖b‖ ‖b₀‖)^k:=by
  intro x
  let m:=mass G p.partSize u
  let T:=max ‖b‖ ‖b₀‖
  have mh:0≤m:=Finset.sum_nonneg fun i _=>mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have th:0≤T:=(norm_nonneg b).trans (le_max_left ..)
  have hi:1≤(1+T)^k:=one_le_pow₀ (by linarith)
  have hh (q:ChartVars F G)(hq:‖q‖≤T):‖x q‖≤m*(1+T)^k:=by
    refine (WilsonPositionProgramAngularDirection.original F p.partSize k p.partSize_le u q).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) mh
  have both:=max_le (hh b (le_max_left ..)) (hh b₀ (le_max_right ..))
  change 1+max ‖x b‖ ‖x b₀‖≤(1+m)*(1+T)^k
  linarith

theorem original (F:Forest g)(h:(ℝ×Exterior.fieldDir G f 1)→ℝ)(k v:ℕ)(ε:ℝ)(he:0≤ε)
    (bound:∀d≤k,∀x y,|Assembly.jet h d (1,x)-Assembly.jet h d (1,y)|≤ε*(1+max ‖x‖ ‖y‖)^v)
    (b b₀:ChartVars F G):
    |invoice (axisLog F) h k b b₀|≤price G k v*(ε*(1+max ‖b‖ ‖b₀‖)^(k*v)):=by
  unfold invoice price
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(k.factorial:ℝ)⁻¹),mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sums
  intro p _
  dsimp only
  apply sums
  intro u _
  let a:=mass G p.partSize u
  let x:=fun q:ChartVars F G=>angular (fun j=>part (axisLog F) (p.partSize j) q) u
  let T:=1+max ‖b‖ ‖b₀‖
  have hx:1+max ‖x b‖ ‖x b₀‖≤(1+a)*T^k:=landed F k p b b₀ u
  have dy:=bound p.length p.length_le (x b) (x b₀)
  have po:0≤1+max ‖x b‖ ‖x b₀‖:=by positivity
  have tested:=dy.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ po hx v) he)
  rw [mul_pow,←pow_mul] at tested
  let w:=weights (fun j=>clock (p.partSize j))
  rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg p.length.factorial : (0:ℝ)≤p.length.factorial)]
  calc
    _ ≤ (|w u| * (p.length.factorial:ℝ))*(ε*((1+a)^v*T^(k*v))):=
      mul_le_mul_of_nonneg_left tested (by positivity)
    _ = _ :=by change (|w u| * _)*(ε*((1+a)^v*T^(k*v)))=(|w u| * _)*(1+a)^v*(ε*T^(k*v));ring

end YM.Integration.WilsonPositionProgramCurvedAngularPrice
end
