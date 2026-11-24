import YM.Integration.WilsonPublicForkIndependentFee

/-! Each converted independent output coefficient is tested on a smooth
separated kernel from the actual matched prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkCoefficientIntegral
open Function Filter Set MeasureTheory Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open FVA2.O FVA2.O.Score FVA2.O.Project MS MS.Land MS.Fleet MS.Theater PowerSeries
open WilsonMSDictionaryFarRead
open scoped Classical Topology BigOperators
variable {G:Gauge}{n h:ℕ}(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)
  (box:Set (Points n))(compact:IsCompact box)(spread:box⊆conf n)

include ms compact spread

theorem coefficient (u:Scan G n)(b:Dframe.Toon G h)(k:ℕ):
    ∃c:ℝ,0≤c ∧ ∀ψ:Test n,tsupport ψ⊆box →
    ‖coeff k (converted Z M ν u ψ (Dframe.flash b))‖≤c*(∫x:Points n,‖ψ x‖):=by
  let target:=Canon.FarCoefficients (Measure.outlook Z.scheme Z.criterion) u
  let row:=fun x=>coeff k (target x (Dframe.flash b))
  have reg:ContinuousOn row box:=((ms.separatedOPE ν).wilson.far u).2.1 _ k |>.mono spread
  obtain ⟨c,cap⟩:=(compact.image_of_continuousOn reg.norm).bddAbove
  refine ⟨max 0 c,le_max_left _ _,?_⟩
  intro ψ inside
  rw [converted_eq Z M ν ms];simp only [Canon.Yield,Read.smearing,coeff_mk]
  change ‖∫x:Points n,ψ x*row x‖≤_
  have mass:Integrable ψ:=ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  rw [mul_comm (max 0 c)]
  refine (norm_integral_le_of_norm_le (mass.norm.mul_const _) (Eventually.of_forall ?_)).trans_eq (integral_mul_const _ _)
  intro x
  by_cases mem:x∈tsupport ψ
  · rw [norm_mul];exact mul_le_mul_of_nonneg_left ((cap (Set.mem_image_of_mem _ (inside mem))).trans (le_max_right _ _)) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport mem]

theorem polynomial (u:Scan G n)(b:Dframe.Toon G h)(q:ℕ):
    ∃c:ℝ,0≤c ∧ ∀(ψ:Test n),tsupport ψ⊆box → ∀t∈Set.Icc (-1:ℝ) 1,
    ‖cutoff q t (converted Z M ν u ψ (Dframe.flash b))‖≤c*(∫x:Points n,‖ψ x‖):=by
  choose c pos priced using fun k=>coefficient Z M ν ms box compact spread u b k
  refine ⟨∑k∈Finset.range (q+1),c k,Finset.sum_nonneg fun k _=>pos k,?_⟩
  intro ψ inside t ht
  have unit:‖(t:ℂ)‖≤1:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_le];exact ht
  unfold cutoff
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul,norm_pow]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) unit)).trans (priced k ψ inside)

end YM.Integration.WilsonPublicForkCoefficientIntegral
