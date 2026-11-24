import YM.Integration.WilsonOriginalRevertedThermalCharge

/-! The actual kinetic read is continuous in a cofinal bank of uniformly bounded field degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalCofinalClock
open Finset Filter Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Moving.Path
open WilsonPositionProgramRadialPrices
open scoped Topology BigOperators

variable {E Z:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]

theorem original (l:Filter Z)(T:UnitCost)(weight:ℤ)(r d:ℕ)(height:ℕ→ℕ)
    (S:Z→Display E)(U:Display E)(finite:∀z,Charge r (fun j=>(height j:ℤ)) (S z))
    (paid:Charge r (fun j=>(height j:ℤ)) U)(x:E)
    (hear:∀j≤r,∀a≤height j,Tendsto (fun z=>S z j ((a:ℝ) • x)) l (𝓝 (U j ((a:ℝ) • x)))):
    Tendsto (fun z=>born (S z) T weight r d x) l (𝓝 (born U T weight r d x)):=by
  let f (z:Z)(j k a:ℕ):=factor (height j) k a*(S z j ((a:ℝ) • x)-U j ((a:ℝ) • x))
  have nodes (j k a:ℕ)(keep:j≤r)(within:a≤height j):Tendsto (fun z=>f z j k a) l (𝓝 (0:ℂ)):=by
    have read:=(hear j keep a within).sub (tendsto_const_nhds (x:=U j ((a:ℝ) • x)))
    simpa only [sub_self,mul_zero] using tendsto_const_nhds.mul (show Tendsto
      (fun z=>S z j ((a:ℝ) • x)-U j ((a:ℝ) • x)) l (𝓝 (U j ((a:ℝ) • x)-U j ((a:ℝ) • x))) from read)
  have panel (j k:ℕ)(keep:j≤r):Tendsto (fun z=>∑a∈range (height j+1),f z j k a) l (𝓝 0):=by
    simpa only [sum_const_zero] using tendsto_finsetSum (range (height j+1)) (fun a ha=>
      nodes j k a keep (mem_range_succ_iff.mp ha))
  let m (j k:ℕ):=motion (money T weight j k) d
  have row (j:ℕ)(keep:j≤r):Tendsto (fun z=>∑k∈range (height j+1),m j k*∑a∈range (height j+1),f z j k a) l (𝓝 0):=by
    simpa only [mul_zero,sum_const_zero] using tendsto_finsetSum (range (height j+1)) (fun k _=>
      (tendsto_const_nhds (x:=m j k)).mul (panel j k keep))
  have high:Tendsto (fun z=>born (S z) T weight r d x-born U T weight r d x) l (𝓝 0):=by
    simp_rw [WilsonOriginalRevertedThermalCharge.restored T weight r d height _ U (finite _) paid x]
    simpa only [sum_const_zero] using tendsto_finsetSum (range (r+1)) (fun j hj=>row j (mem_range_succ_iff.mp hj))
  simpa only [sub_add_cancel,zero_add] using high.add_const (born U T weight r d x)

end YM.Integration.WilsonReceivedDepositedOrbitalCofinalClock
end
