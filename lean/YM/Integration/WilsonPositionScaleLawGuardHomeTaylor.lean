import YM.Integration.WilsonPositionScaleLawGuardHomePrint
import YM.Integration.WilsonPositionScaleLawKineticRatio

/-! On the actual two physical homes the complete prescribed Borel change
has its posted operator polynomial and a uniform positive-axis Taylor bill. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardHomeTaylor
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato FVA2 FVA2.Register
open WilsonPhysicalPositionBornCandidates (record)
open WilsonPositionScaleLawDressedBudget (home)
open WilsonPositionScaleLawGuardHomePrint (tab taylor)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionHomogeneousCoefficients (Warrant)
open scoped Topology Classical BigOperators
variable {G:Gauge}(C:Family G)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "X"=>(Bel C.book).Field

def model (d:ℕ)(g:ℝ):X d→L[ℂ]X d:=1+record G C d (guide G d (WilsonPositionHomogeneousNear.field Z d g))

theorem axis (H:Warrant Z)(d q:ℕ):∃K:ℝ,0≤K ∧ ∀ᶠg:ℝ in 𝓝[>] 0,
    ‖model C Z d g-taylor C Z d q g‖≤K*g^(q+1):=by
  let E:=X d
  letI:NormedAddCommGroup (E→L[ℂ]E):=ContinuousLinearMap.toNormedAddCommGroup
  letI:NormedSpace ℂ (E→L[ℂ]E):=ContinuousLinearMap.toNormedSpace
  letI:NormedSpace ℝ (E→L[ℂ]E):=NormedSpace.restrictScalars ℝ ℂ _
  let V:MoveSpace G d→L[ℝ](E→L[ℂ]E):=(record G C d).toContinuousLinearMap
  obtain ⟨A,hA,paid⟩:=WilsonPositionHomogeneousNear.expansion Z d q
  refine ⟨‖V‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
  filter_upwards [paid] with g bill
  let u:=guide G d (WilsonPositionHomogeneousNear.field Z d g)
  have fit:‖u-tab Z d q g‖≤A*g^(q+1):=bill
  have eq:model C Z d g-taylor C Z d q g=V (u-tab Z d q g):=by
    rw [WilsonPositionScaleLawGuardHomePrint.original C Z H,model,map_sub]
    change (1+V u)-(1+V (tab Z d q g))=V u-V (tab Z d q g)
    abel
  rw [eq]
  exact (V.le_opNorm _).trans ((mul_le_mul_of_nonneg_left fit (norm_nonneg V)).trans_eq (mul_assoc ..).symm)

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
variable (H:Warrant Z)(hG:G.Simple)(funded:Coupling G (kinetic Z F J))
include H hG funded in
theorem original (d q:ℕ):∃K:ℝ,0≤K ∧ ∀ᶠr in trail,
    ‖home F J Z d r-taylor R.family Z d q (kinetic Z F J r)‖≤K*kinetic Z F J r^(q+1):=by
  obtain ⟨K,hK,paid⟩:=axis R.family Z H d q
  have zero:=funded.conforms hG
  have live:Tendsto (kinetic Z F J) trail (𝓝[>] 0):=
    tendsto_nhdsWithin_iff.mpr ⟨zero,funded.positive⟩
  refine ⟨K,hK,?_⟩
  filter_upwards [live.eventually paid,zero.eventually (WilsonPositionHomogeneousNear.invertible Z d)] with r fee good
  have eq:home F J Z d r=model R.family Z d (kinetic Z F J r):=by
    ext v
    exact WilsonPositionScaleLawWholeHome.originalOperator F J Z good v
  rw [eq];exact fee

variable [W:RangeSpec]
theorem homes {P:ℝ→Prop}(p:∀ᶠr in trail,P r):
    ∀ᶠz:ℝ×Ratio in sweep,∀r∈({z.1,z.2.val*z.1}:Finset ℝ),P r:=by
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually p,
    WilsonPositionScaleLawCompactNative.bothHomes.eventually p] with z a b r hr
  rcases Finset.mem_insert.mp hr with e|e
  · exact e.symm ▸ a
  · exact (Finset.mem_singleton.mp e).symm ▸ b

include H hG funded in
theorem both (d q:ℕ):∃K:ℝ,0≤K ∧ ∀ᶠz:ℝ×Ratio in sweep,∀r∈({z.1,z.2.val*z.1}:Finset ℝ),
    ‖home F J Z d r-taylor R.family Z d q (kinetic Z F J r)‖≤K*kinetic Z F J r^(q+1):=by
  obtain ⟨K,hK,fee⟩:=original Z F J H hG funded d q
  exact ⟨K,hK,homes fee⟩

end YM.Integration.WilsonPositionScaleLawGuardHomeTaylor
