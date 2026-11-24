import YM.Integration.WilsonPublicForkIndependentReceipts
/-! One uniform independently calculated coefficient panel. The far label can
include a predeclared scale-dependent finite field change with its own price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIndependentPanel
open Filter Function Set Finset MeasureTheory FVA2 FVA2.O FVA2.O.Score FVA2.Register FVA2.Scale
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Theater RG17 Trace.Pilot
open WilsonMSDictionaryFarRead WilsonMSDictionaryVector WilsonPublicForkIndependentPlacement
open WilsonPublicForkIndependentFields
open scoped Classical Topology BigOperators
variable {G:Gauge}(C:Family G){n:ℕ}(d:Fin n→ℕ)(h:ℕ)
  (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)
  {I:Type}[Fintype I]
include ν ms in
theorem original (g:ℝ→ℝ)(physical:Coupling G g)(K:Set (Points n))(closed:IsCompact K)(inside:K⊆conf n)
    (φ:I→Test 2)(outer:ℝ→I→Free C h)(E:ℕ)(c:ℝ)(cp:0≤c)
    (outerPaid:∀ᶠ r in trail,∀j,‖outer r j‖*(g r)^E≤c):
    ∃D:ℝ,0≤D ∧ ∀q P A:ℕ,P+E<A → P+E+A*(2*h+1)<q+1 →
     ∀ᶠr in trail,∀(v:∀i,Free C (d i))(ψ:Test n),tsupport ψ⊆K → ∀j,
       let y:=prediction C d h Z M ν v ψ q (g r)
       let H:=full C d h Z q (g r) (age A (g r)) v (outer r j) ψ (φ j)
       let G:=gram C h Z q (g r) (age A (g r)) (outer r j) (φ j)
       ‖H-∑k,(WilsonMSDictionaryVector.basis C h).repr y k*G k‖≤
         (D*((∏i,‖v i‖)*Read.Value ψ))*(g r)^(P+A*(2*h+1)):=by
  obtain ⟨basisCost,bp,charged⟩:=budget C d h
  let measure:=∑j,Read.Value (φ j)
  have mp:0≤ measure:=Finset.sum_nonneg fun j _=>Read.value_0 _
  refine ⟨basisCost*c*measure,mul_nonneg (mul_nonneg bp cp) mp,?_⟩
  intro q P A margin high
  have rows:=eventually_all.mpr fun j=>WilsonPublicForkIndependentFields.original C d h Z M ν ms g physical
    q (P+E) A margin high K closed inside (φ j)
  filter_upwards [rows,outerPaid,physical.positive] with r paid far gp v ψ compact j
  dsimp only
  have near:0≤∏i,‖v i‖:=Finset.prod_nonneg fun _ _=>norm_nonneg _
  have exact:0≤(g r)^(P+A*(2*h+1)):=pow_nonneg gp.le _
  have height:Read.Value (φ j)≤ measure:=Finset.single_le_sum (fun k _=>Read.value_0 (φ k)) (Finset.mem_univ j)
  have duration:(g r)^(P+E+A*(2*h+1))=(g r)^E*(g r)^(P+A*(2*h+1)):=by rw [←pow_add];congr 1;omega
  refine (paid j v (outer r j) ψ compact).trans ?_
  rw [duration]
  have total:=mul_le_mul_of_nonneg_right (charged v (outer r j)) (Read.value_0 ψ)
  have bill:=mul_le_mul total height (Read.value_0 _) (by positivity)
  refine (mul_le_mul_of_nonneg_right bill (mul_nonneg (pow_nonneg gp.le _) exact)).trans ?_
  calc
    _=(basisCost*(∏i,‖v i‖)*Read.Value ψ*measure*(g r)^(P+A*(2*h+1)))*(‖outer r j‖*(g r)^E):=by ring
    _≤(basisCost*(∏i,‖v i‖)*Read.Value ψ*measure*(g r)^(P+A*(2*h+1)))*c:=
      mul_le_mul_of_nonneg_left (far j) (by have:=Read.value_0 ψ;positivity)
    _=_:=by ring

end YM.Integration.WilsonPublicForkIndependentPanel
