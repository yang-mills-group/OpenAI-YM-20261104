import YM.AllOrder.Carillon.Carve
import YM.AllOrder.High.Canon
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir

/-!
# F4: high valuation with rebased path phase (parameters β γ independent).

Variants of High/{Canon}. Transfer within Hull later by
aligned Career (identity) before the beta-read; pointwise. For applications
with Coast binding Y-axis family across β can instead follow Trio.Card via
catalog choices. Don't assert analytic matching on the indicated Budget yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Carillon
open High
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M k j m π u d: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
local notation "B" => radiusB p
local notation "τ" => Mint.width X.halo (radiusB p) (radiusB p)
open Meadow (Park spin)

section plane
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
variable (F : Finset H.fragrances) (χ:Chi)
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)

/-- Symmetrization independent of BudgetPoint choice (`paths.site = s.2`). -/
def centerC (k:ℕ) (β γ : ℝ) := Meadow.atlas ((fun x V=> ∑ i∈F.filter (fun i=> x∈perf H i), -(((perf H i).card:ℝ))⁻¹* stream H χ V i)+ Meadow.garner T.down T.low β γ B k)
lemma newC_turns (k:ℕ) (β γ:ℝ) : Trio.Mirrors (centerC F χ k β γ):= fun i s v U=> Meadow.astrolabe _ _ _ (s,v)

def unheardC (k:ℕ) (β γ: ℝ) (z:Magazine H) : Config G c→ℝ := if z∈blossom F k then 0 else hymn H χ β γ z
def linger (k:ℕ) (β γ:ℝ) : Collection.Source G c:= ⟨choir (unheardC F χ k β γ) ∘ pennant H,(organ H χ β γ).hardRead⟩

lemma newC_ledger (β γ:ℝ) (i:ℕ) : (linger F χ k β γ).logRead i=(if i∈ foliage F k then 0 else (organ H χ β γ).logRead i) := by
  unfold linger organ choir; let y:= Song.pennant H i; change Rim c • ((unheardC _ _ _ _ _ _) ∘ y.1.view)=_; unfold unheardC; split
  · rename_i he; rw [if_pos ((High.leaves ..).2 he)]; ext; simp
  next hz=> rw [if_neg (fun h=> hz ((High.leaves ..).1 h))]; rfl

variable (Y : BudgetPoint)
lemma newC_coffer (β γ:ℝ) (x:Site c) (V:Config G c) :
    (∑ i∈F.filter (fun i=> x∈perf H i), -(((perf H i).card:ℝ))⁻¹* stream H χ V i) + Meadow.garner T.down T.low β γ B k x V=∑ i∈blossom F k, Meadow.share H Y x i * hymn H χ β γ i V:= by
  unfold blossom; rw [sum_disjSum,sum_map]; apply congr_arg₂ HAdd.hAdd
  · rw [sum_filter]; apply sum_congr rfl; intro i hi
    change _=(if x∈ perf H i then _ else _) * (-1*stream H χ V ((Match.staple (H:=H) (J:=H) rfl rfl rfl).furrow i)); rw [flip_noop]; split_ifs <;> ring
  unfold Meadow.garner; rw [Finset.sum_product]; dsimp only [Meadow.share,Sum.elim]; change _=∑ s:Seat c,∑ i∈_, (if (strings T.down Y (Meadow.legs s i)).site=x then (1:ℝ) else 0)* hymn H χ β γ (.inr (Meadow.legs s i)) V
  rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _; rw [sum_comm]; apply sum_congr rfl; intro _ _; simp only [ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,↓reduceIte]; rfl
lemma newC_bound_frame (β γ:ℝ) (x:Site c): centerC F χ k β γ x= ∑ i∈foliage F k, Meadow.garnerAt H Y x i • ((organ H χ β γ).logRead i) := by
  funext V; unfold centerC Meadow.atlas; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; unfold likely; unfold foliage; rw [sum_map,sum_product]; simp only [Equiv.toEmbedding_apply]; simp_rw [newC_coffer F χ Y β γ, Finset.mul_sum]; apply sum_congr rfl; intro θ _; apply sum_congr rfl; intro i _
  dsimp only [organ, Meadow.garnerAt, Meadow.honor,Function.comp_apply,smul_eq_mul]; rw [Equiv.apply_symm_apply]; let q:= Meadow.share H Y ((spin θ).symm x) i; let v:=hymn H χ β γ i (θ.view V); change Rim c*(q*v)=q*(Rim c*v); ring
variable (hB:Y.B=radiusB p) (hc:∀ i∈F,∀ x∈perf H i,perf H i ⊆ neighbors d x) (h : radiusB p + radiusB p ≤ d)
include hc h hB
lemma newC_section_frame (β γ:ℝ) {y t:ℝ} (hp : Collection.Local (posting Y H) Y (organ H χ β γ) t y) (x:Site c): Y.Regular (neighbors d x) (centerC F χ k β γ x) := by
  rw [newC_bound_frame F χ Y]; apply Meadow.regularA _; intro i hi; by_cases hF:Meadow.garnerAt H Y x i=0; · rw [hF,zero_smul]; exact CouplingShape.reg_const _
  have hM:= (artists F Y hB hc h x i hi hF).2; rw [Beam.rewrite_rule] at hM; exact CouplingShape.reg_scale _ (CouplingShape.reg_extend (hp.smooth i) hM)
end plane

end YM.AllOrder.Carillon
