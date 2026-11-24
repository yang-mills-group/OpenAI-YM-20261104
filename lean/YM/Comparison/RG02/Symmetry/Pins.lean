import YM.Comparison.RG02.Symmetry.Code
import YM.AnalyticNext.CUBIC_MATCH.Ward
import YM.AnalyticNext.CUBIC_MATCH.Lift.Pair
import YM.Push.LOOP_COEFFICIENT.Color
import Mathlib.Analysis.Analytic.IsolatedZeros
/-!
# Actual displacements and first-unmatched potential legs

At any order on torus local prescription. Derive group-path Ward including anchored generator of
any displacement in the image of `dColor`. This suffices for every tensor leg in first unmatched
order when subtracting previously matched invariant packets. Doesn't **factor** a resulting tensor
through d/curl or cost projection on paths. Also no global translation/inversion/lifts asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry.Orbit
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Moving Moving.Path Moving.Shift Marker Multi Order YM.Next.SectorChange Integral Actual Laplace Valence Ribbon YM.CubicMatch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} (u : fieldDir G c 0) (x : fieldDir G c 1)
local notation "X"=> fieldDir G c 1
local notation "L"=> (dColor G c 0)
-- displacement B(t,h), using dSlope & previous CubicMatch rooted sign
private def l (t:ℝ): Config G c:= gauge (rootTurn u t) (represent (t • x))
def descent (t:ℝ): X:= dslope (logged ∘ l u x) 0 t
private lemma originates : l u x 0=1:= by unfold l; rw [zero_smul, Precision.link_one,turn_zero]; exact gauge_trivial _
private lemma l_smooth (i:Edge (Site c)) : ContDiffAt ℝ ω (fun t:ℝ=> G.mat (l u x t i)) 0:= gauged_smooth (u:=fun t:ℝ=> t • x) (by fun_prop) (turn_smooth u (v:=id) contDiffAt_id) i
lemma descent_smooth : glows (descent u x) := by
    have he : AnalyticAt ℝ (logged ∘ l u x) 0:= (logged_smooth (originates u x) (l_smooth u x)|>.analyticAt)
    obtain ⟨p,H⟩:= he
    exact (show AnalyticAt ℝ (descent u x) 0 from ⟨_,H.has_fpower_series_dslope_fslope⟩).contDiffAt
lemma descends : descent u x 0=x+ L u := by rw [descent,dslope_same]; exact (turns_through x u).deriv
lemma ascendance : Flow (descent u x) (fun _=>x):= by
    have h: Continuous (rootTurn u):= by unfold rootTurn; fun_prop
    have he := h.tendsto 0; rw [turn_zero] at he
    refine ⟨1,rootTurn u, he.mono_left (show along≤𝓝 0 from nhdsWithin_le_nhds),?_⟩
    have ht:= read_logged (originates u x) (l_smooth u x)
    filter_upwards [(show ∀ᶠ t in along,represent (logged (l u x t))=l u x t from ht.filter_mono nhdsWithin_le_nhds)] with t hz
    have h(x':ℝ): x' • descent u x x'=logged (l u x x'):= by simpa [originates,descent] using sub_smul_dslope (logged ∘ l u x) 0 x'
    unfold sample; rw [h t]; exact hz
open Matrix in
lemma weight (d:ℝ) : L (d • u)= d • (L u) := by
    funext i; ext j; change (Exterior.d _ c *ᵥ parts G 0 (d • u) j) i=d*(Exterior.d _ c *ᵥ parts G 0 u j) i
    rw [show parts G 0 (d • u) j=d • parts G 0 u j from rfl, Matrix.mulVec_smul]; rfl

variable {r k n : ℕ} {p q:ℕ→fieldDir G c 1 → ℂ}
lemma Sheet.offset (h : Sheet r p) (H : Sheet r q) (he : ∀ i<k,p i=q i) (hk : k≤r) : (p k-q k) (x+L u)=(p k-q k) x:= by
    rw [← descends u x]; exact h.unmatched H (descent_smooth u x) contDiffAt_const (ascendance u x) hk he
lemma Sheet.displace (h : Sheet r p) (H : Sheet r q) (he : ∀ i<k,p i=q i) (hk : k≤r) : fderiv ℝ (p k-q k) x (L u)=0 := by
    let g:= p k-q k; have ht(t:ℝ): g (x+t • L u)=g x:= weight u t ▸ h.offset (t • u) x H he hk
    let f(t:ℝ):= x+t• L u; have hf0: f 0=x:=by simp [f]
    have hg: ContDiff ℝ ω g := (h.known k hk).sub (H.known k hk)
    have hx:= (show DifferentiableAt ℝ g (f 0) from hg.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 (show HasDerivAt f (L u) 0 from by simpa [f] using ((hasDerivAt_id' (0:ℝ)).smul_const (L u)).const_add x)
    rw [hf0,show g ∘ f = fun _ => g x from funext ht] at hx; exact hx.unique (hasDerivAt_const ..)
lemma Sheet.closes (h : Sheet r p) (H : Sheet r q) (he : ∀ i<k,p i=q i) (hk : k≤r) : (iteratedFDeriv ℝ (n+1) (p k-q k) x).curryLeft (L u)=0 := by
    let g:= p k-q k; have hg: ContDiff ℝ ω g := (h.known k hk).sub (H.known k hk)
    apply ContinuousMultilinearMap.ext; intro v; rw [ContinuousMultilinearMap.curryLeft_apply, Analysis.cons_inner (hg.contDiffAt.of_le le_top), show Analysis.D (L u) g=fun _=>0 from funext fun a=>h.displace u a H he hk]; simp

-- Color identity for every sheet eff form; derives all-order absent linear rank even when
-- mark. moments with explicit weight factor handled by the same method.
lemma coloring (s:G.El): Flow (fun (_:ℝ)=> recolor s 1 x) (fun _=>x) := by
   refine ⟨s,(fun _ _=> s),tendsto_const_nhds,Eventually.of_forall ?_⟩
   intro t; unfold sample; rw [← map_smul (recolor s 1),recolor_one]
private lemma patrol_const (k:ℕ) : patrol k p (fun _=>x)=p k x:= by unfold patrol; simp only [Function.comp_def]; simp_rw [mconst]; rw [sum_ite_eq', if_pos (mem_range_succ_iff.mpr (Nat.zero_le _)), Nat.sub_zero]
lemma Sheet.color (h : Sheet r p) (he:k≤r) (s:G.El) : p k (recolor s 1 x)= p k x:= by rw [← patrol_const (p:=p), ← patrol_const (p:=p) x, h.follows _ _ (coloring x s) contDiffAt_const contDiffAt_const k he]
set_option maxHeartbeats 500000 in
lemma Sheet.color_grad (h : Sheet r p) (he:k≤r) (hG:G.Simple) : fderiv ℝ (p k) 0=0:= by
   let L' := (fderiv ℝ (p k) 0).toLinearMap
   have h(v:X)(z:G.El): L' (recolor z 1 v)=L' v := by
      let f:= recolor (n:=c) z 1
      have ht : p k∘ f=p k:= funext fun x=> h.color x he z; have hp : DifferentiableAt ℝ (p k) (f 0) := (h.known k he).differentiable (by simp) _
      have hv := fderiv_comp (𝕜:=ℝ) 0 hp f.differentiableAt; rw [ht,f.map_zero, f.fderiv] at hv; exact (DFunLike.congr_fun hv v).symm
   let load (x : Exterior.Body 1 c): G.Color →ₗ[ℝ] fieldDir G c 1 := LinearMap.single ℝ (fun _ : Exterior.Body 1 c => G.Color) x
   have hp(x b): L' (load x b)=0:= by
      have he (u:G.El)(v:G.Color): recolor u 1 (load x v)= load x (G.adjoint u v):= by
         rw [show load x v = (Pi.single x v) from rfl,show load x (G.adjoint u v)= (Pi.single x (G.adjoint u v)) from rfl]; exact CubicMatch.colored_single ..
      have hx:= Push.Loops.invariant_null hG (L'.comp (load x)) (fun u v=> by simp only [LinearMap.comp_apply,← he]; exact h _ u)
      exact DFunLike.congr_fun hx b
   apply ContinuousLinearMap.ext; intro v; rw [show v=∑ i, load i (v i) from funext fun i=> by rw [Finset.sum_apply]; simp [load,Pi.single_apply] ]; change L' _ =0; simp_rw [_root_.map_sum L',hp,sum_const_zero]
end YM.Comparison.RG02.Symmetry.Orbit
