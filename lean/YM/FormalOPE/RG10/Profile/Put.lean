import YM.FormalOPE.RG10.Profile.Sheets
import YM.FormalOPE.RG10.Profile.CompactIntegral

/-! # Riemann integration principle for fixed-compact separated tests.
Uses the anchored Native offsets and the solved Baire/complete criterion. No $$ \int \mathord{\bullet} $$
interpretation into Fréchet-valued Bochner functions required; we identify the limit pointwise. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function Set TopologicalSpace MeasureTheory Filter Topology Metric ContDiffMapSupportedIn
open PertExtension.LatticePT Grid
open scoped Topology ContDiff Distributions Classical BigOperators BoundedContinuousFunction
variable {E F : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F]
    {K:Compacts E}{n:ℕ}
local notation "chart" => slide (E:=E) (F:=F) (K:=K)
variable {q:ℕ+} (L:Points n → 𝓓_{K}(E, F))(h: Continuous L) (hL:HasCompactSupport L)

def purse (m:ℕ) := epsilon q m ^ (4*n) • ∑ i, L (Grid.sample q m i)
include h hL
lemma put (hq:1<q.val) : ∃ L': 𝓓_{K}(E,F), Tendsto (purse (q:=q) L) atTop (𝓝 L') ∧ (∀ x, L' x=∫ y, L y x) := by
 let g (i:ℕ) : Points n→ E →ᵇ (E [×i]→L[ℝ] F) := structureMapCLM ℝ ⊤ i ∘ L
 let Q i:= ∫ y, g i y
 have hp (i:ℕ): HasCompactSupport (g i):=by
   exact hL.comp_left ((structureMapCLM ℝ ⊤ i).map_zero)
 have he : Tendsto (chart∘ purse (q:=q) L) atTop (𝓝 Q):= by
   refine tendsto_pi_nhds.mpr fun i=>?_ ; change Tendsto (fun m=> structureMapCLM ℝ ⊤ i (purse (q:=q) L m)) _ (𝓝 (Q i)); simp_rw [purse,map_smul,map_sum]
   let G (m:ℕ) := epsilon q m ^ (4*n) • ∑ a,g i (Grid.sample q m a); have hv := weighted hq (g i) ((structureMapCLM ℝ ⊤ i).continuous.comp h) (hp i); change Tendsto G atTop (𝓝 (Q i)); exact hv
 obtain ⟨f,hf⟩:= slideClosed.isClosed_range.mem_of_tendsto he (Eventually.of_forall fun m=>mem_range_self _)
 have ht:Tendsto (purse (q:=q) L) atTop (𝓝 f):= slideClosed.isEmbedding.tendsto_nhds_iff.mpr (hf ▸ he)
 refine ⟨f,ht,fun x=>?_ ⟩
 let l : 𝓓_{K}(E,F) → F:= fun u=> u x
 have hl:Continuous l:= by unfold l; fun_prop
 apply tendsto_nhds_unique ((hl.tendsto f).comp ht)
 dsimp only [Function.comp_def,l]; simp only [purse,smul_apply,sum_apply]
 apply weighted (f:=fun y=> l (L y)) hq _ (hL.comp_left (show l 0=0 from rfl))
 exact hl.comp h
end YM.FormalOPE.RG10.Profile
