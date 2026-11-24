import YM.OPE.Compatible.Hatch.Tear
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
-- directional photograph at floor k goes to unbounded exterior patient rows, with loss polynomial.
variable {I:Type}{A:I→ Side}{φ:Filter I}{Z:I→ℝ}{W:I→ℕ}{a c b':ℝ}(U:Scaffold φ Z A W r)
variable (q p: GlyphQ G A)
open Scaffold
lemma jet_zoom {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](c:ℝ)(p:E→ℝ)(x:E)(k:ℕ): jet p k (c • x)= c^k* jet p k x:=by unfold jet; rw [(iteratedFDeriv ℝ k p 0).map_smul_univ (fun _=>c) (fun _=>x)]; simp [mul_left_comm]
lemma PhiHeight (p:Bid.Dir G n→ℝ)(hp:∀ x:Bid.Dir G n, Roster x ≤ 1→ ‖p x‖ ≤ a) (hz:∀ (t:ℝ) x,p (t • x)= t^k * p x) (x:Bid.Dir G n)(ht:0 < c)(he:Roster x ≤ c): ‖p x‖ ≤ a*c^k:=by
        let y:= c⁻¹ • x; have h:x=c • y:=(smul_inv_smul₀ ht.ne' _).symm; rw [h,hz,norm_mul,Real.norm_of_nonneg (by positivity)]; rw[mul_comm]; apply mul_le_mul_of_nonneg_right _ (by positivity); apply hp; unfold y; rw [herm,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (inv_mul_cancel₀ ht.ne')
variable (h:Shor U q p)
variable (V:(i:I)→Board (A i) (r+1))(i:↥(fieldP r))(u:G.ColorIndex)
noncomputable abbrev Tfoil (j:I) : Chamber G r→L[ℝ] Bid.Dir G (A j):= sailT G (V j)
noncomputable abbrev Cpit (G:Gauge) (A:I→Side)(W:I→ℕ) (i:I): Bid.Dir G (A i)→L[ℝ] Bid.Dir G (A i):= SillV _ _ (W i+1)
set_option quotPrecheck false
local notation "R!"=> Tfoil (G:=G) V
local notation "B!"=> Cpit G A W
noncomputable def PivotQ (j:I)(x:Bid.Dir G (A j))(y:Chamber G r):= fderiv ℝ (q j) x ((R!) j y)
noncomputable abbrev Budγ (k:ℕ)(j:I)(x:Bid.Dir G (A j))(y:Chamber G r):=PivotQ (Article q (k+1)) V j x y
-- phase.Up
include h
lemma αke (j:I)(x:Bid.Dir G (A j))(k:ℕ): Budγ q V k j x (An i (Phone G) u)=Article (rerun i.val u q) k j x:=by
        unfold Budγ PivotQ Tfoil; have hv:=LoopGen (G:=G) (V j) i u; rw [hv]; unfold Scaffold.rerun tfan; exact vast (q j) k (h.smooth_f j) (functorE 0 i.val u) x
lemma ζPass (k:ℕ)(a:ℝ):
        ∃ r t:I→ℝ,RateLE φ Z r 0∧RateLE φ Z t a∧∀ᶠ j in φ,∀ x:Bid.Dir G (A j),∀ c:ℝ,0<c→ Roster x ≤ c→ let y:= PickL G (i,u); let f(p):= Budγ q V k j p y; ‖f x‖ ≤ r j*c^k∧ ‖f x-f ((Cpit G A W j) x)‖ ≤ t j *c^k:=by
           let z:=Article (rerun i.val u q) k; let p':= Article (rerun i.val u p) k; let R:=h.rim i u k a; let Y:=h.rim i u k 0; have he: Photos φ Z 0 z:= ((Y.1.green (Filμ.See U.top Y.2) U.top.fair)).cone (Eventually.of_forall fun i=> congr_fun (sub_add_cancel z p') i)
           obtain ⟨C,hC,H⟩:=he.cost; obtain ⟨t,ht,hT⟩:= R.1.cost; refine ⟨C,t+t,hC,ht.add ht U.top.fair,?_⟩; filter_upwards [H,hT,R.2.here] with j hi hx hh x c ht hv; intro y f
           have hm : f= z j:=funext fun x=>αke U q p h V i u j x k; rw [hm]; let X:= B! j; let S:= X x; have hS:z j x-z j S= (z j x-p' j x) - (z j S - p' j S):=by have hp:p' j x=p' j S:= hh.jury _ _ (wind x (U.top.room j).board _ (fun _ h=>h)).symm; rw [hp]; abel
           have hk(w:Bid.Dir G (A j))(h:Roster w ≤ c): ‖z j w-p' j w‖ ≤ t j*c^k:=PhiHeight (z j-p' j) hx (fun u y=>by simp only [z,p',Pi.sub_apply,Article,jet_zoom,mul_sub]) w ht h
           rw [hS]; exact ⟨PhiHeight (z j) hi (fun t y=>jet_zoom ..) x ht hv, (norm_sub_le ..).trans ((add_le_add (hk _ hv) (hk _ ((saltP x _).trans hv))).trans_eq (add_mul ..|>.symm))⟩
end Sleeve
end YM.OPE.Merchant
