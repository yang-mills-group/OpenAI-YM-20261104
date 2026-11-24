import YM.Comparison.RG02.Moving.Cargo
/-!
# Polynomial transport gives moving Wick coefficient identity

Before taking logarithm. Evaluation and radial jet in A perform diagonal Taylor terms on the
appropriate finite r. Curvature stencils and marker print algebra come later on the
*same* coefficients. Only uses genuine Q of the ideal supply; when adopting cutQ in budget use
 again with the cut input data valuation (certain short primitive quadratic mismatches
 mustn't then be included). Any quantitative use leaving unmasked ideal requires different
 estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree YM.Next.Rank
open YM.Precision YM.Next.SectorChange Gaussian Affinity Matrix Cumulants
open PertExtension.Series PertExtension.Series.Tested Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I J : Type} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype I] [DecidableEq I]
variable [FiniteDimensional ℝ X] [Fintype V]

namespace Cargo
variable (x:X) (l:Hot R→ℕ) (F:Hot R→House X I→ℂ) (f:House X I→ℝ)
    (r : ℕ)
local notation "E" => House X I
local notation "♯"=> Assembly.prescription ((1,x,0):E) (reach X) l F
local notation "Pt"=> Normal.poly I
variable (s : R.Mode) (C:Field X I)
lemma dash : ∀ᶠ t in 𝓝 (0:ℝ), Cloud.wick (C.Q 0) (C.symmetric 0) 0 (manifesto x l F f r s C t)=(value (t:ℂ) (cost x l F f r C t)).part s := (path_home x).eventually (C.rotated.and C.B_lives) |>.mono (fun i hi=> shift_gaussian x l F f r s C i hi.1 hi.2)

variable {f l F}
local notation "Ψ"=> Assembly.rows (Assembly.expansions l F (C.retax f)) s
local notation "Γ"=> (Assembly.numeric l F (C.retax f))
local notation "ξ"=> (fun i=> F i ∘ C.vibe.effect)
local notation "e'"=> (C.vibe.price f)
local notation "χ"=> Assembly.numeric l ξ e'
local notation "φ"=> manifesto x l F (C.retax f) r s C
variable (hf : Ray (C.Q 0) f) (hF : ∀ i, GradeAt (l i) (F i))

private lemma fleet (v:I→ℝ) : ContinuousAt (fun t:ℝ=> C.link x t *ᵥ v) 0 := by
   let q := (C.link x)
   have h : ContDiffAt ℝ ω (C.link x) 0 := (Eq.mp (by rw [path0 x]:ContDiffAt ℝ ω C.B 0=ContDiffAt ℝ ω C.B (path x 0)) C.B_smooth).comp 0 (smooth_path x).contDiffAt
   apply (continuousAt_pi).mpr; intro i; unfold Matrix.mulVec dotProduct; exact tendsto_finsetSum _ fun j _=> (YM.Push.Loops.matrix_component h i j).continuousAt.mul continuousAt_const
-- keep pure marks along for the coefficient comparison. doesn't assert a uniform bound.
include hf hF
lemma transform_bill (v : I→ℝ) : Bill (r+1) (fun t=> (χ t (season x v)).part s-Cloud.paint v (φ t)):= by
   let p:= fun t=>season x (C.link x t *ᵥ v)
   have H := ((Assembly.radial_comparison l F (C.retax f) (funded (C.upholds hf).root hF) zero_lt_one) s).fits r
   let Y t := (Γ t (p t)).part s
   have ht:= Path.encounter (p:=p) (by unfold Radial.shade; fun_prop) (continuousAt_const.add continuous_norm.continuousAt) ((season_cont ..).continuousAt.comp (fleet x C v)) H
   change Bill (r+1) (fun t=> Y t-Zone.eval Ψ r t (p t)) at ht
   refine bill_congr ?_ ht
   filter_upwards [(path_home x).mono_left nhdsWithin_le_nhds|>.eventually (C.B_lives.and C.rotated),Tested.eventually_pos] with t h hp
   rw [manifesto_read]; unfold Y; rw [show Γ t (p t)=χ t (season x v) from C.present x hp.ne' h.2 h.1 hf v]

omit hf [Fintype V] in
private lemma smooth_vibe : ∀ i, GradeAt (l i) ((F i) ∘ C.vibe.effect) := fun i=> (hF i).coarse C.vibe.no_jets.2 C.vibe.base
local notation "D"=>Assembly.rows (Assembly.expansions l ξ e') s
lemma charged_trial (v : I→ℝ) : Trial (fun k=> Assembly.rows (Assembly.expansions l ξ e') s k (season x v))
    (fun t=> Cloud.paint v (φ t)) r := by
   have hp:= Path.encounter (p:=fun _=> season x v) (by unfold Radial.shade; fun_prop) (continuousAt_const.add continuous_norm.continuousAt) continuousAt_const (((radial_comparison l ξ e' (funded (C.vibe.prices hf).root (smooth_vibe C hF)) zero_lt_one) s).fits r)
   have hh:= bill_add hp (bill_neg (transform_bill x r s C hf hF v))
   apply bill_congr _ hh
   refine Eventually.of_forall fun t=> ?_
   let a k:=D k (season x v); change (χ t (season x v)).part s-peval a r t + -((χ t (season x v)).part s-_)=_ - peval a r t; abel

-- target canonical forecast of *unrotated* field-tag system.
theorem leads (k : ℕ) (he : k≤r) : detail (♯ f (C.Q 0) (C.symmetric 0) r) s k = Path.motion (fun t:ℝ=> (value (t:ℂ) (cost x l F (C.retax f) r C t)).part s) k := by
   rw [Affinity.Door.agree x (C.Q 0) C.flat C.vibe hf hF] -- switch only in proof
   let Q:= C.Q 0
   let L:= Cloud.wick Q (C.symmetric 0) 0
   obtain ⟨p,H⟩:= (manifesto_smooth x l F (C.retax f) r s C).assay 1 k
   have hz : L ∘ φ=ᶠ[𝓝 0] (fun t:ℝ=> (value (t:ℂ) (cost x l F (C.retax f) r C t)).part s) := dash x l F (C.retax f) r s C
   have hs (v:I→ℝ) : D k (season x v)=Cloud.paint v p := by
      let L' := (Cloud.paint v).toLinearMap; let A:= charged_trial x r s C hf hF v
      exact (trial_gap A (Path.ordinary (((manifesto_smooth x l F (C.retax f) r s C).known L').of_le le_top) r) k he).trans (H L')
   rw [show Path.motion _ _= L p from ?_]
   · rw [detail,Assembly.order_read (I:=I) _ _ _ _ _ _ _ C.flat s he]; unfold Assembly.insideMoment; unfold season at hs; simp_rw [hs]
     have hh := (Cloud.paid Q (C.symmetric 0) C.flat.posSemidef 0 p).2; simp_rw [zero_add,Cloud.shift_zero] at hh; exact hh
   rw [← H L]; unfold Path.motion Assembly.jet; rw [(hz.iteratedFDeriv ℝ k).eq_of_nhds]
end Cargo
end YM.Comparison.RG02.Moving
