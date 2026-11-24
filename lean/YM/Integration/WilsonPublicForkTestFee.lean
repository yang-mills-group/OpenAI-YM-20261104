import YM.Integration.WilsonPublicForkCoefficientIntegral

/-! One test and source norm on a fixed separated compact covers the
whole finite independent quotient, including the output unit and lowers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkTestFee
open Filter Function Finset Set MeasureTheory Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open FVA2.O FVA2.O.Score FVA2.O.Project MS MS.Land MS.Fleet MS.Theater RG17
open WilsonMSDictionaryFarRead WilsonMSDictionaryVector WilsonPublicForkIndependentFee
open scoped Classical BigOperators Topology
variable {G:Gauge}(C:Family G){n:ℕ}(d:Fin n→ℕ)(h:ℕ)
    (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)

theorem fee_le (y:Free C h):
    dose C h y ≤ (∑k,‖((WilsonMSDictionaryVector.basis C h).coord k).toContinuousLinearMap‖)*‖y‖:=by
  unfold dose
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k _=>((WilsonMSDictionaryVector.basis C h).coord k).toContinuousLinearMap.le_opNorm y

include ms in
theorem original (box:Set (Points n))(compact:IsCompact box)(spread:box⊆conf n)(q:ℕ):
    ∃K:ℝ,0 ≤ K ∧ ∀(v:∀i,Free C (d i))(ψ:Test n),tsupport ψ⊆box → ∀t∈Set.Icc (-1:ℝ) 1,
    dose C h (prediction C d h Z M ν v ψ q t) ≤ K*(∏i,‖v i‖)*(∫x:Points n,‖ψ x‖):=by
  let b:=WilsonMSDictionaryVector.basis C
  let A:=∀i,Dframe.Toon G (d i)
  let u:=fun (j:A) i=>Dframe.flash (j i)
  choose c cp price using fun (j:A) (k:Dframe.Toon G h)=>
    WilsonPublicForkCoefficientIntegral.polynomial Z M ν ms box compact spread (u j) k q
  let op:=fun j:A=>∏i,‖((b (d i)).coord (j i)).toContinuousLinearMap‖
  let col:=fun j:A=>∑k,c j k*‖b h k‖
  let outer:=∑j:A,op j*col j
  let roof:=∑k,‖((b h).coord k).toContinuousLinearMap‖
  have room:0 ≤ roof:=Finset.sum_nonneg fun k _=>((b h).coord k).toContinuousLinearMap.opNorm_nonneg
  have opPos(j:A):0 ≤ op j:=Finset.prod_nonneg fun i _=>((b (d i)).coord (j i)).toContinuousLinearMap.opNorm_nonneg
  have colPos(j:A):0 ≤ col j:=Finset.sum_nonneg fun k _=>mul_nonneg (cp j k) (norm_nonneg _)
  refine ⟨roof*outer,mul_nonneg room (Finset.sum_nonneg fun j _=>mul_nonneg (opPos j) (colPos j)),?_⟩
  intro v ψ inside t ht
  let size:=∏i,‖v i‖
  let mass:=∫x:Points n,‖ψ x‖
  let a:=fun (j:A) (k:Dframe.Toon G h)=>cutoff q t (converted Z M ν (u j) ψ (Dframe.flash k))
  have sizePos:0 ≤ size:=Finset.prod_nonneg fun _ _=>norm_nonneg _
  have massPos:0 ≤ mass:=integral_nonneg fun _=>norm_nonneg _
  have term(j:A):‖∑k,a j k • b h k‖ ≤ col j*mass:=by
    refine (norm_sum_le _ _).trans ?_
    dsimp only [col];rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (price j k ψ inside t ht) (norm_nonneg _)).trans_eq (by ring)
  have factors(j:A):‖∏i,(b (d i)).repr (v i) (j i)‖ ≤ op j*size:=by
    dsimp only [op,size];rw [norm_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>((b (d i)).coord (j i)).toContinuousLinearMap.le_opNorm _)
  have gross:‖prediction C d h Z M ν v ψ q t‖ ≤ outer*size*mass:=by
    change ‖∑j:A,(∏i,(b (d i)).repr (v i) (j i)) • (∑k,a j k • b h k)‖ ≤ _
    refine (norm_sum_le _ _).trans ?_
    dsimp only [outer];rw [Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_smul]
    exact (mul_le_mul (factors j) (term j) (norm_nonneg _) (mul_nonneg (opPos j) sizePos)).trans_eq (by ring)
  exact (fee_le C h _).trans ((mul_le_mul_of_nonneg_left gross room).trans_eq (by ring))

theorem inversion (box:Set (Points n))(compact:IsCompact box)(spread:box⊆conf n)(q:ℕ):
    let P:=((ms.separatedOPE ν).wilson.light h).choose
    ∃K:ℝ,0 ≤ K ∧ ∀(v:∀i,Free C (d i))(ψ:Test n),tsupport ψ⊆box → ∀t∈Set.Icc (-1:ℝ) 1,
    ∀δ:ℝ,0<δ → ∀ᶠ s:ℝ in atTop,
    dose C h (experiment C d h Z M ν v ψ P q t s) ≤ K*(∏i,‖v i‖)*(∫x:Points n,‖ψ x‖)+δ:=by
  dsimp only
  obtain ⟨K,kp,read⟩:=original C d h Z M ν ms box compact spread q
  refine ⟨K,kp,?_⟩
  intro v ψ inside t ht δ dp
  have live:=((ms.separatedOPE ν).wilson.light h).choose_spec.2
  exact ((continuous_dose C h).continuousAt.tendsto.comp (experiment_limit C d h Z M ν v ψ ms _ live q t)).eventually
    (ge_mem_nhds (lt_of_le_of_lt (read v ψ inside t ht) (lt_add_of_pos_right _ dp)))

end YM.Integration.WilsonPublicForkTestFee
