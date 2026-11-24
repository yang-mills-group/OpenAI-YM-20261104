import YM.Integration.WilsonPositionScaleLawGuardLift

/-! Finite-dimensional tested coordinate control of full operator coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardCoordinates
open Function Filter Set Finset
open scoped Classical BigOperators Topology
variable {T E:Type*}[TopologicalSpace T][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]

theorem vector (a:T→E)(h:∀l:Module.Dual ℂ E,Continuous (fun t=>l (a t))):Continuous a:=by
  let b:=Module.finBasis ℂ E
  have eq:a=(fun t=>∑i,b.coord i (a t) • b i):=funext fun t=>(b.sum_repr (a t)).symm
  rw [eq]
  exact continuous_finsetSum _ fun i _=>(h (b.coord i)).smul continuous_const

theorem operator (a:T→E→L[ℂ]E)(h:∀x:E,∀l:Module.Dual ℂ E,Continuous (fun t=>l (a t x))):
    Continuous a:=by
  let b:=Module.finBasis ℂ E
  let build (i:Fin (Module.finrank ℂ E)):E→ₗ[ℂ](E→L[ℂ]E):={
    toFun:=fun y=>((b.coord i).smulRight y).toContinuousLinearMap
    map_add':=fun x y=>by ext v;change b.coord i v • (x+y)=b.coord i v • x+b.coord i v • y;rw [smul_add]
    map_smul':=fun z x=>by ext v;change b.coord i v • (z • x)=z • (b.coord i v • x);rw [smul_comm]}
  have eq:a=fun t=>∑i,build i (a t (b i)):=by
    funext t;ext x
    rw [_root_.sum_apply]
    change a t x=∑i,b.coord i x • a t (b i)
    calc
      _=a t (∑i,b.coord i x • b i):=congrArg (a t) (b.sum_repr x).symm
      _=_:=by rw [map_sum];simp only [map_smul]
  rw [eq]
  exact continuous_finsetSum _ fun i _=>(build i).continuous_of_finiteDimensional.comp
    (vector (fun t=>a t (b i)) (h (b i)))

end YM.Integration.WilsonPositionScaleLawGuardCoordinates
