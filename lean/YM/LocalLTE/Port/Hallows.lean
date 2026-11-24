import YM.LocalLTE.Units.Oracle
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Wind
/-! # Summing at a fixed finite legacy. No dimension cost lost (we do not want quantitative posture for the coefficients per se; we buy it at the next RG step). Keep all derivatives and norms on the SAME domain, on the coordinates in which they have been proved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open ConnectedActivityE6
open PhysicalNext.Repeat FrameBox Cabana Push
open Progress.DirectedRecipe
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{n : Side}{s:Support n}{o:Site n}(X:Grove o)(t k:ℕ) (κ:ℝ) (R:BudgetPoint)
variable (s)
def polymer : Pkt (Directions G n) k →ₗ[ℝ] (Config G n→ ℝ) where
   toFun := FrameBox.realise X t κ
   map_add' f g:= funext fun u=> congr_fun (actual_add f g) (X.crook t Push.SectorMeasure.Chi.canonical κ u)
   map_smul' r v:= funext fun _=> congr_fun (actual_smul r v) _
abbrev cord:= polymer (G:=G) X t k κ
-- enough image finite.Mount on chart with ALL raw jets.Inf.T.
def screen : Submodule ℝ (Pkt (Directions G n) k) where
   carrier:= {f| R.Regular s (cord X t k κ f)}
   zero_mem' :=by rw [Set.mem_setOf_eq,map_zero]; exact unspent ..
   add_mem' := by
       intro x y hx hy; rw [Set.mem_setOf_eq,map_add]; let f:=(cord X t k κ x); let g:=(cord X t k κ y); have hh(i:Config G n) (h:Healthy R.threshold s i): Local.Chart R.order (f+g) i:=(hx.smooth i h).add (hy.smooth i h)
       exact ⟨fun _ _ h=> congr_arg₂ (·+·) (hx.sites _ _ h) (hy.sites _ _ h),hx.borel.add hy.borel,fun t V=> congr_arg₂ (·+·) (hx.symmetry ..) (hy.symmetry ..),hh,fun U h a l ht=> Next.Foundations.left_has _ ht (hh U h)⟩
   smul_mem' := by
       intro r f h; rw [Set.mem_setOf_eq,map_smul]; let V:= (cord X t k κ f)
       have hh(i)(hi:Healthy R.threshold s i): Local.Chart R.order (r • V) i:= contDiffAt_const.mul (h.smooth i hi)
       exact ⟨fun _ _ ht=>congr_arg (r*·) (h.sites _ _ ht), measurable_const.mul h.borel,fun i u=> congr_arg (r*·) (h.symmetry i u),hh,fun U h a l ht=> Next.Foundations.left_has _ ht (hh U h)⟩
local notation "Y"=> screen s X t k κ R
-- include spatial ALL(up to)
abbrev WaysQ (X:BudgetPoint)(G:Gauge){n:Side}(s:Support n) (o:Site n):= {u:Config G n× List (Directions G n)// Healthy X.threshold s u.1∧ u.2.length ≤ X.order ∧ ∀ i∈u.2,X.dirBound o i}
variable (o':Site n)
local notation "F"=> WaysQ R G s o'
def levels (i: Config G n→ℝ) (q: F):ℝ:= leftDerivs i q.val.2 q.val.1
def universeL : (screen (G:=G) s X t k κ R) →ₗ[ℝ] (F→ℝ) where
   toFun i:=levels s R o' (cord X t k κ i.val)
   map_add' i j:=by funext q; change leftDerivs (cord X t k κ (i.val+j.val)) _ _=_; rw [map_add]; exact Local.left_add _ ((show R.Regular s _ from i.property).smooth _ q.property.1) ((show R.Regular s _ from j.property).smooth _ q.property.1) q.property.2.1
   map_smul' c i:= by funext q; change leftDerivs (cord X t k κ (c • i.val)) _ _=_; rw [map_smul]; exact Local.left_linear (c • ContinuousLinearMap.id ℝ ℝ) _ ((show R.Regular s _ from i.property).smooth _ q.property.1) q.property.2.1
-- coverage h. ζ aggregator doesn't need any statement about existence norms Off-curves. Return representation with same ALL.Hence.
lemma themed {I:Type*}(f:I→ Config G n→ ℝ) (e:I→ℝ)(he:Summable e)(hv:∀ i,∃ Pkt',f i=polymer X t k κ Pkt'∧ R.Regular s (f i) ∧ R.supBounds o' s (f i) (e i)) : ∃ P, let v:=polymer X t k κ P; R.Regular s v ∧ R.supBounds o' s v (∑' i,e i) ∧ ∀ u, HasSum (fun i=> levels s R o' (f i) u) (levels s R o' v u):=by
    choose Q h hX hE using hv; let g(i):=f i; let y(i:I):Y:= ⟨Q i,(by change R.Regular s (polymer X t k κ (Q i)); rw [← h]; exact hX _)⟩; let Z:= universeL (G:=G) s X t k κ R o'
    have hu(i):Z (y i) = levels s R o' (f i):=by rw [h];rfl
    have hb (p:F)(i): ‖Z (y i) p‖ ≤ e i:= hu i ▸ (hE i).2 p.val.1 p.property.1 p.val.2 p.property.2.1 p.property.2.2 -- edit
    let C (p:F):= ∑' i,Z (y i) p
    have hG (p:F): Summable fun i=> ‖Z (y i) p‖:= he.of_nonneg_of_le (fun _=> norm_nonneg _) (hb p)
    have hs : HasSum (Z ∘ y) C:= by apply tendsto_pi_nhds.mpr; intro i; simpa only [Function.comp_def,Finset.sum_apply] using! ((hG i).of_norm.hasSum)
    have hFD : FiniteDimensional ℝ (screen (G:=G) s X t k κ R):=by infer_instance
    have hx: C∈LinearMap.range Z:= (LinearMap.range Z).closed_of_finiteDimensional.mem_of_tendsto hs (Eventually.of_forall fun I=> Submodule.sum_mem (LinearMap.range Z) fun i _=>⟨y i,rfl⟩)
    obtain ⟨Q',hz⟩:=hx
    refine ⟨Q'.val,Q'.property,⟨tsum_nonneg fun i=> (hE i).1,fun V h l hl ht=>?_⟩,?_⟩
    · let j : F:= ⟨(V,l),h,hl,ht⟩; change ‖Z Q' j‖ ≤ _; rw [hz]; unfold C; exact (norm_tsum_le_tsum_norm (hG j)).trans ((hG j).tsum_le_tsum (hb j) he)
    intro j; change HasSum _ (Z Q' j); rw [hz]; exact ((hG j).of_norm.hasSum).congr_fun (fun i=> congr_fun (hu i).symm j)
end YM.LocalLTE.Port
