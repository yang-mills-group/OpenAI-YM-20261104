import YM.Integration.WilsonMovingForkCanonicalKernels

/-! The genuine independently prescribed ordinary and two-point arrays are
integrals of their finite position kernels on the actual reflected tests. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkKernelIntegrals
open Filter Function Set Finset MeasureTheory FVA2 FVA2.O FVA2.Register Maxwell XSpace XSpace.Normalize
open MS MS.Land MS.Fleet MS.Theater MS.Rake RG17 PhysMS Trace.Pilot
open FVA2.O.Project FVA2.Scale FVA2.O.Score FVA2.O.Enh WilsonPublicForkIndependentWindow WilsonPublicForkIndependentPlacement
open WilsonMSDictionaryVector WilsonMovingForkCanonicalKernels WilsonPublicForkIndependentFields
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open private whole from YM.Integration.WilsonPublicForkTestProduct
open scoped Classical Topology BigOperators
variable {G:Gauge}(C:Family G){n:ℕ}(d:Fin n → ℕ)(h:ℕ)
  (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)

def fullAt (q:ℕ)(g s:ℝ)(v:∀i,Free C (d i))(a:Free C h)(p:Points n×Points 2):ℂ:=
  ∑j,load C d v j*∑u,(WilsonMSDictionaryVector.basis C h).repr a u*many Z q g s (fun i=>Dframe.flash (j i)) (unitScan h u) p

def gramAt (q:ℕ)(g s:ℝ)(a:Free C h)(k:Dframe.Toon G h)(z:Points 2):ℂ:=
  ∑u,(WilsonMSDictionaryVector.basis C h).repr a u*pair Z q g s (unitScan h u) k z

private theorem finite {X ι:Type*}[MeasureSpace X][Fintype ι](w:X → ℂ)(f:ι → X → ℂ)(c:ι → ℂ)
    (paid:∀i,Integrable (fun x=>w x*f i x)):
    (∑i,c i*(∫x,w x*f i x))=∫x,w x*(∑i,c i*f i x):=by
  calc
    _=∑i,∫x,c i*(w x*f i x):=by simp only [integral_const_mul]
    _=∫x,∑i,c i*(w x*f i x):=(integral_finsetSum _ (fun i _=>(paid i).const_mul (c i))).symm
    _=_:=integral_congr_ae (Eventually.of_forall fun x=>by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring)

private theorem local_test {l:ℕ}(φ:Test l)(u:Points l → ℂ)(c:ContinuousOn u (tsupport φ)):
    Integrable (fun x=>φ x*u x):=by
  let a:=fun x=>φ x*u x
  have comp:=φ.hasCompactSupport
  have paid:Integrable ((tsupport φ).indicator a):=
    ((φ.continuous.continuousOn.mul c).integrableOn_compact comp).integrable_indicator comp.measurableSet
  convert paid using 1
  funext x
  by_cases hx:x∈tsupport φ
  · simp only [indicator_of_mem hx,a]
  · simp only [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport hx,zero_mul]

include ν ms in
theorem original (q:ℕ)(g s:ℝ)(ψ:Test n)(φ:Test 2)
    (fit:∀p∈space ψ φ,forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1)):
    (∀v a,full C d h Z q g s v a ψ φ=tested ψ φ (fullAt C d h Z q g s v a)) ∧
    (∀a k,gram C h Z q g s a φ k=φ.applyTo (gramAt C h Z q g s a k)):=by
  obtain ⟨rich,one⟩:=WilsonMovingForkCanonicalKernels.regular (h:=h) Z M ν ms q g s ψ φ fit
  constructor
  · intro v a
    let W:=fun p:Points n×Points 2=>ψ p.1*φ p.2
    let B:=fun (j:Modes (G:=G) d)(u:Dframe.Toon G h)=>many Z q g s (fun i=>Dframe.flash (j i)) (unitScan h u)
    let c:=fun u=>(WilsonMSDictionaryVector.basis C h).repr a u
    have cont(j:Modes (G:=G) d)(u:Dframe.Toon G h):ContinuousOn (B j u) (space ψ φ):=rich _ _
    have pad(j:Modes (G:=G) d):Integrable (fun p=>W p*(∑u,c u*B j u p)):=by
      apply whole ψ φ
      exact continuousOn_finsetSum _ (fun u _=>continuousOn_const.mul (cont j u))
    change (∑j,load C d v j*(∑u,c u*(∫p,W p*B j u p)))=∫p,W p*(∑j,load C d v j*(∑u,c u*B j u p))
    simp_rw [finite W (B _) c (fun u=>whole ψ φ (cont _ u))]
    exact finite W _ _ pad
  · intro a k
    exact finite _ _ (fun u=>(WilsonMSDictionaryVector.basis C h).repr a u) (fun u=>local_test φ _ (one (unitScan h u) k))

end YM.Integration.WilsonMovingForkKernelIntegrals
