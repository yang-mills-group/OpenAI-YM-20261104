import YM.Integration.WilsonThermometerWeakProbeTest

/-! The shrinking smoothing scale is chosen after the signed row names its
finite external order. This gives a fixed derivative demand before the regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakProbeScale
open Filter Topology
open scoped Topology
def size (b:ℕ)(t:ℝ):ℝ:=t^(((b+1:ℕ):ℝ)⁻¹)
theorem original (b Q:ℕ){t:ℝ}(pos:0<t)(small:t≤1):
    0<size b t ∧ size b t≤1 ∧
    t^(Q+1)*(size b t)⁻¹^b≤t^Q ∧ size b t^((b+1)*Q+1)≤t^Q:=by
  have h:0<size b t:=Real.rpow_pos_of_pos pos _
  have le:size b t≤1:=Real.rpow_le_one pos.le small (by positivity)
  have pay:size b t^(b+1)=t:=by
    rw [size,←Real.rpow_natCast,←Real.rpow_mul pos.le]
    rw [inv_mul_cancel₀ (by positivity : ((b+1:ℕ):ℝ)≠0),Real.rpow_one]
  refine ⟨h,le,?_,?_⟩
  · have line:t*(size b t)⁻¹^b=size b t:=by
      calc t*(size b t)⁻¹^b = size b t^(b+1)*(size b t)⁻¹^b:=congrArg (fun v=>v*(size b t)⁻¹^b) pay.symm
           _ = size b t:=by rw [pow_succ,inv_pow];field_simp [(pow_pos h b).ne']
    rw [pow_succ,mul_assoc,line]
    exact mul_le_of_le_one_right (by positivity) le
  · rw [pow_succ,pow_mul,pay]
    exact mul_le_of_le_one_right (by positivity) le

theorem shrinks {A:Type*}{l:Filter A}{g:A→ℝ}(b:ℕ)(limit:Tendsto g l (𝓝 0)):
    Tendsto (fun r=>size b (g r)) l (𝓝 0):=by
  let t:ℝ:=(((b+1:ℕ):ℝ)⁻¹)
  have pos:0<t:=by dsimp [t];positivity
  have c:= (Real.continuous_rpow_const pos.le).continuousAt (x:=(0:ℝ)) |>.tendsto.comp limit
  change Tendsto ((fun x:ℝ=>x^t) ∘ g) l (𝓝 0)
  simpa only [Real.zero_rpow pos.ne'] using c
end YM.Integration.WilsonThermometerWeakProbeScale
end
