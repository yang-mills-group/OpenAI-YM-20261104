import YM.LocalLTE.FieldPT.Val
/-! Film.Photo symbolic $j≤2$ p.Immutable. Keep selected and exact analytic forecasts within
 complete cost index. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset MeasureTheory
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {j z k m i:ℕ} {W κ K U C V t H: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
open Scene
variable {a:RegularAddress n}(X:Art a z)(p:BudgetPoint)(f:ℝ→Pot G n)(s:ℝ) {r:ℝ}
local notation "W"=> X.radius
local notation "g"=> Scene.tallyF X.grove f
set_option quotPrecheck false
local notation "H!" => fun (t:ℕ)(s: J k)=> play X κ (Scene.kernelF X.grove f t X.radius s)
-- tag.La.Frame. general Kernel.
def banner (κ:ℝ) (s:J k)(i:Fin m): Pot G n:= play X κ (kernelF X.grove f i.val W s)
local notation "x!" s=> banner (k:=k) (m:=m) X f κ s
lemma quota (κ:ℝ)(s:J k)(i:Fin m) (h:kernelF X.grove f i.val W s=0) : banner X f κ s i=0:=by change playL X κ i.val _=0; rw [h,map_zero]
variable (h:Reliable G κ K) (hs: ∀ s∈Weft.clip, p.Regular a.support (f s))(hp:Scene X.grove κ X.radius k m f C)
include hp h hs p
lemma scarves (u:J k) : pick k f u=∑ i:Fin m,banner X f κ u i:=by
    exact Weft.picked (Price.ensemble X p f h hp hs) u
lemma advance {s:ℝ}(hx:s∈Weft.clip) : f s=∑ u:J k,∑ i:Fin m, Weft.mark k u s • banner X f κ u i:=by
   rw [hp.weft.seen hx]; simp_rw [← Finset.smul_sum]; apply sum_congr rfl; intro i h'; rw [scarves X p f h hs hp i] -- edit
omit hs hp
section grades
variable (hg:∀ s∈Weft.clip, Comic G a p (f s))(hG:G.Simple)
omit h in
include hg hG in
lemma role (u:J k)(v:ℕ)(hf:v<2) : kernelF X.grove f v W u=0:=by
   refine sum_eq_zero (s:=Finset.univ (α:=J k)) (?_)
   intro i _; let j:= probe k i; let l:= f j ∘ Grove.soloV; obtain ⟨hc,hL,hv⟩:= hg _ (Weft.probes k i); change _ • (Scene.tallyF X.grove f v X.radius j)=0; unfold tallyF Tensor.coeff; suffices hh: iteratedFDeriv ℝ v (l ∘ X.grove.shore X.radius) 0=0 by rw [show f j∘Grove.soloV ∘ X.grove.shore X.radius=(l ∘ X.grove.shore X.radius) from rfl,hh,smul_zero,smul_zero]
   apply norm_le_zero_iff.mp; rcases (show v=0 ∨ v=1 from by omega) with h|h <;> subst v
   · rw [norm_iteratedFDeriv_zero, Function.comp_apply, map_zero]; unfold l; rw [Function.comp_apply,Hall.zeroSolo,hL,norm_zero]
   have ht: DifferentiableAt ℝ l 0:= by unfold l; rw [← Hall.bare]; exact (germ_diff hc).differentiableAt (by decide)
   have he: fderiv ℝ l 0=0:=by unfold l; rw [← Hall.bare]; exact flat_critical hG hc
   rw [norm_iteratedFDeriv_one,fderiv_comp _ (by rw [map_zero]; exact ht) (ContinuousLinearMap.differentiableAt _),map_zero,he,ContinuousLinearMap.zero_comp,norm_zero]
include hp h hg hG
lemma filmPlot (u:J k)(v:Fin m) : Comic G a p (banner X f κ u v):=by
    by_cases hL:v.val=2; swap
    · rcases lt_or_gt_of_ne hL with hh|hh; rw [Price.quota X f _ u v (Price.role X p f hg hG u v hh)]; exact Price.flick p
      exact lowG X p _ hh h
    let v' i:=banner X f κ u (i:Fin m); let Z:= ∑ i∈(univ : Finset (Fin m)).erase v,v' i
    have hv: Comic G a p (Weft.pick k f u):= Price.Comic.totals univ fun i _=> (hg _ (Weft.probes k i)).weight _
    have hx: Comic G a p Z:= Price.Comic.totals _ fun i hi=> ?_
    · rw [show banner X f κ u v=pick k f u-Z from (by rw [scarves X p f h (fun s hs=> (hg _ hs).1) hp u]; have he:v' v+Z=∑ i,v' i:= Finset.add_sum_erase _ _ (mem_univ _); exact eq_sub_of_add_eq he)]; exact hv.pair hx
    -- combo
    · have hh:i.val ≠2:=fun hh=> (Finset.ne_of_mem_erase hi) (Fin.ext (hh.trans hL.symm))
      rcases lt_or_gt_of_ne hh with hk|hk
      · unfold v'; rw [Price.quota X f _ u i (Price.role X p f hg hG u i hk)]; exact Price.flick p
      exact Price.lowG X p _ hk h
end grades
end YM.AnalyticBridge.VerifiedReset.Collection.Price
