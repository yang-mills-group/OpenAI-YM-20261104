import YM.OPE.Compatible.Hatch.Veux
/-! # Cost transport into orthogonal cube. Projection preserves Hardy plateau. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
open Aloof
namespace Sleeve
variable {I:Type}{A:I→ Side}{φ:Filter I}{Z:I→ℝ}{W:I→ℕ}{a c b':ℝ}(U:Scaffold φ Z A W r)
variable (q p: GlyphQ G A)
open Scaffold
variable (h:Shor U q p)(V:(i:I)→Board (A i) (r+1))
variable (L:I→ Law (Chamber G r))
open Merchant.SiteL
local notation "R!"=> Tfoil (G:=G) V
local notation "B!"=> Cpit G A W
set_option maxHeartbeats 200000
private lemma JourneyQ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](x y:E)(f:E→ℝ)(hx:Differentiable ℝ f)(t:ℝ) (h:∀ z∈Set.Icc (0:ℝ) 1, ‖fderiv ℝ f (x + (z:ℝ) • y) y‖ ≤ t) : ‖f (x+y)-f x‖ ≤ t:=by
        let F(z:ℝ):=f (x+z • y); have hz(r:ℝ):HasDerivAt F (fderiv ℝ f (x+r • y) y) r:= (hx _).hasFDerivAt.comp_hasDerivAt (f:=fun t:ℝ=>x+t • y) r (by simpa using! ((hasDerivAt_id' r).smul_const y).const_add x)
        let S:= Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℝ) (f:=F) (C:=t) (fun v _=> (hz v).differentiableAt) (fun v hy=>by rw [(hz _).deriv];exact h _ hy) (convex_Icc 0 1) (show (0:ℝ)∈Set.Icc 0 1 from ⟨le_rfl,zero_le_one⟩) (show (1:ℝ)∈Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩)
        simpa [F,norm_sub_rev] using! S
private lemma F_tr (j:I)(x:Bid.Dir G (A j))(y:Chamber G r)(a:ℝ)(ha:a∈Set.Icc (0:ℝ) 1) :Roster (x+a • (sailT G (V j) y)) ≤ Roster x+‖y‖:=by
        apply (rAdd ..).trans; rw [herm]; apply add_le_add le_rfl; exact (mul_le_of_le_one_left (ros _) (by rw[Real.norm_of_nonneg ha.1]; exact ha.2)).trans ((spice _).trans (sailX G _ y))
include h
noncomputable def OpX (j:I)(x:Bid.Dir G (A j))(y:Chamber G r):= q j (x+sailT G (V j) y) -q j x
-- precise exposure OpX, Price.Vol through suppressed ETH calibration.
lemma JFair (k:ℕ):∃ t:I→ℝ,RateLE φ Z t 0∧∀ᶠ i in φ,∀ (x:Bid.Dir G (A i))(y:Chamber G r)(f:ℝ),0<f→Roster x+‖y‖≤f→ ‖OpX (Article q (k+1)) V i x y‖ ≤ t i*f^k*‖y‖:=by
       obtain ⟨t,ht,H⟩:=PISeen U q p h V k; refine ⟨t,ht,?_⟩; filter_upwards [H] with i hi x y f hf hz; let R:=Article q (k+1) i; have hh:R = jet (q i) (k+1):=rfl; have hp: Bond R:= tallJ (k+1) (q i) 0; refine JourneyQ x (sailT G (V i) y) R (hp.smooth.differentiable (by simp)) _ ?_; exact fun z h=> hi _ f hf ((F_tr V i x y z h).trans hz) y
omit h in private lemma archZ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (F:E→ℝ)(R:E→L[ℝ] E)(x y:E)(v:ℝ)(hv:R y=y)(hf:Differentiable ℝ F)(hz:∀ t:ℝ,t∈Set.Icc (0:ℝ) 1→let a:=x+t • y; ‖fderiv ℝ F a y-fderiv ℝ F (R a) y‖≤v): ‖F (x+y)-F x-(F (R x+y)-F (R x))‖ ≤ v:=by
        let D:=F-F∘R; have he:Differentiable ℝ (F∘R):=hf.comp R.differentiable; have hA: F (x+y)-F x-(F (R x+y)-F (R x))=D (x+y)-D x:=by unfold D; simp only[Pi.sub_apply,Function.comp_apply,map_add,hv];ring
        rw[hA]; refine JourneyQ x y D (hf.sub he) v fun t ht=>?_ ; unfold D; rw [fderiv_sub (hf _) (he _),_root_.sub_apply, fderiv_comp _ (hf _) (R.differentiable _),R.fderiv,ContinuousLinearMap.comp_apply,hv]; exact hz t ht
omit h in
private lemma priced_arc {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (D : E → ℝ) (R : E →L[ℝ] E) (S : Y →L[ℝ] E)
    (size : E → ℝ) (x : E) (y : Y) (f v : ℝ) (scale : R (S y) = S y)
    (hd : Differentiable ℝ D) (shape : ∀ z ∈ Set.Icc (0:ℝ) 1, size (x+z • S y) ≤ f)
    (paid : ∀ w, size w ≤ f → ‖((fderiv ℝ D w).comp S) y-((fderiv ℝ D (R w)).comp S) y‖ ≤ v) :
    ‖D (x+S y)-D x-(D (R x+S y)-D (R x))‖ ≤ v := by
  apply archZ D R x (S y) v scale hd
  exact fun z hz => paid (x+z • S y) (shape z hz)

lemma JAnchor (k:ℕ):∃ t:I→ℝ,RateLE φ Z t a∧∀ᶠ i in φ,∀ (x:Bid.Dir G (A i))(y:Chamber G r)(f:ℝ),0<f → Roster x+‖y‖ ≤ f → ‖OpX (Article q (k+1)) V i x y-OpX (Article q (k+1)) V i ((Cpit G A W i) x) y‖ ≤ t i*f^k*‖y‖:=by
  obtain ⟨t, ht, H⟩ := VDeep (a:=a) U q p h V k
  refine ⟨t, ht, ?_⟩
  filter_upwards [H] with i hi x y f hf hz
  let D := Article q (k+1) i
  have hd : Differentiable ℝ D := (show Bond D from tallJ (k+1) (q i) 0).smooth.differentiable (by simp)
  have position z (hZ : z ∈ Set.Icc (0:ℝ) 1) := (F_tr V i x y z hZ).trans hz
  have quote w (hw : Roster w ≤ f) := hi w f hf hw y
  unfold OpX
  with_reducible_and_instances
    exact priced_arc D (Cpit G A W i) (sailT G (V i)) Roster x y f (t i*f^k*‖y‖)
      (Sill_sail _ y (Nat.succ_le_of_lt (U.top.room i).wide)) hd position quote
end Sleeve
end YM.OPE.Merchant
