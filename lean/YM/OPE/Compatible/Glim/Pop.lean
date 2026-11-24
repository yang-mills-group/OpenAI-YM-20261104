import YM.OPE.Compatible.Glim.Event
/-! # suppress below seam even for broad marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
variable {n:Side}(H:Even n.val)(T:Plot H)(p:T.Free)(x:Site n){t l c:ℝ}
local notation "L!"=> chestZ H T (G:=G)
local notation "E!"=> Keys G T.Free
variable (i:G.ColorIndex){r m k:ℕ}
local notation "Q!"=>Page (Shade G) r
local notation "µ"=>(n.val:ℝ)^m
lemma wealthInsert (U:Script (Shade G) r) (h:soot m U l)(w:Fin r)(X: Keys G T.Free)(hx:BeamNear H T p x c)(hc:0≤c):
     (n.val:ℝ)^m* ‖orchestra U x (Function.update (fun _=> L! X) w (L! (bop H T p i)))‖ ≤ l * (c^m*(1+‖X‖)^r) :=by
       let d:= Function.update (fun _:Fin r=> L! X) w (L! (bop H T p i)); let f(j:Q!):= U j* render x j d; let u:ℝ:=c^m*(1+‖X‖)^r; have he:HasSum f (orchestra U x d):=instruments U (sootS h) x d; have hv:0≤u:= by unfold u; positivity
       have hs(j:Q!): µ *‖f j‖ ≤ (Page.figure m j* ‖U j‖)*u:=by
            unfold f; rw [norm_mul, mul_left_comm]; exact (mul_le_mul_of_nonneg_left (Crumble H T p x i hx hc m X r j w) (norm_nonneg _)).trans_eq (by unfold u;ring)
       rw [← he.tsum_eq]; apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm he.summable.norm) (by positivity :0≤(n.val:ℝ)^m)).trans; rw [← tsum_mul_left]; apply ((he.summable.norm.mul_left ((n.val:ℝ)^m)).tsum_le_tsum hs (h.2.1.mul_right u)).trans; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 hv
noncomputable abbrev flora (U:Script (Shade G) r) (x:Site n) (H:Even n.val)(T:Plot H): Keys G T.Free→ℝ:= Tensor.diagonal (orchestra U x) ∘ chestZ H T
lemma floraC(U:Script (Shade G) r):ContDiff ℝ ω (flora U x H T):= (Tensor.diag_smooth _ _).comp (chestZ H T (G:=G)).contDiff -- macro
lemma floc (U:Script (Shade G) r)(h:soot m U l)(X:Keys G T.Free)(hx:BeamNear H T p x c)(hc:0≤c):
    (n.val:ℝ)^m*‖fderiv ℝ (flora U x H T) X (bop H T p i)‖ ≤ r * (l*(c^m*(1+‖X‖)^r)):=by
       let P:E!→L[ℝ] (Fin r→ deck (Shade G) n):= ContinuousLinearMap.pi fun _=> L!; let f:=orchestra U x; let z:=bop H T p i; change _*‖fderiv ℝ (f ∘ P) X z‖≤ _; erw [(f.hasFDerivAt (P X) |>.comp X P.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply,ContinuousMultilinearMap.linearDeriv_apply]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)); rw [mul_sum]; apply (Finset.sum_le_sum (g:=fun _=>l*(c^m*(1+‖X‖)^r)) ?_).trans_eq; rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fin]; intro j _; exact wealthInsert H T p x i _ h j X hx hc
open Drift Char Silt Silt.Float
variable {u:ℕ}{τ:Phase→ℕ}
abbrev Nyx (v:Drift.Tower (Shade G) u τ): ScriptJ E!:=Stand.charted T (cutφ H v x)
lemma nib (v: Tower (Shade G) u τ)(j:Phase): (fun X:E!=> (Nyx H T x v X).seq j.val)=fun X=>∑ r ∈ range (u+j.val+1),flora (lilies (τ j) (u+j.val) (Shade G) (v j) r) x H T X :=by
    funext X; change (inkM (spread _ _ _ v) _ _ _).seq _=_; rw [vein_i]; let F:=lilies (τ j) (u+j.val) (Shade G); change Flair (F (v j)) _ (L! X) x= _; unfold Flair; apply Finset.sum_congr rfl; intro i _; exact (instruments _ (sootS ((sproutV (τ j) (u+j.val) (v j)).2 i)) x _).tsum_eq
abbrev LidFee(u:ℕ):ℝ:= (u+3:ℝ)^2
lemma payNib (v: Tower (Shade G) u τ)(j:Phase)(h:m ≤ τ j)(hc:0≤ c)(hp:BeamNear H T p x c)(X:Keys G T.Free):
     (n.val:ℝ)^m* ‖fderiv ℝ (fun X:E!=> (Nyx H T x v X).seq j.val) X (bop H T p i)‖ ≤ LidFee u * c^m*‖v‖ *(1+‖X‖)^(u+2):=by
        let W:=u+j.val+1; let f:=lilies (τ j) (u+j.val) _ (v j); let Rex(r:ℕ):=flora (f r) x H T; have hpV(r): soot m (f r) ‖v‖:= ((Rill.soot_le_k _ _ (sproutV (τ j) _ (v j)|>.2 r) h)).tips (norm_le_pi_norm v j)
        rw [nib H T x v j,show (fun X:E!=> ∑ i∈range W,flora _ _ _ _ _)=fun X=>∑ i∈range W,Rex i X from rfl, fderiv_fun_sum (A:=Rex) (fun i _=>(floraC H T x _).differentiable (by simp) _), _root_.sum_apply]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity));rw [mul_sum];let D:ℝ:=W*(‖v‖*(c^m*(1+‖X‖)^(u+2))); have hw: W≤u+3:=(by unfold W; have:= j.isLt;omega);apply (sum_le_sum (g:=fun _=>D) (fun s hs=>?_)).trans; swap; · have ht:s < W:=mem_range.mp hs; apply (floc H T p x i _ (hpV s) X hp hc).trans; unfold D;gcongr <;>first|positivity|omega|simp
        rw [sum_const,nsmul_eq_mul,card_range]; unfold D; rw[←mul_assoc]; refine (mul_le_mul_of_nonneg_right (show (W:ℝ)*W ≤ LidFee u from ?_) (by positivity)).trans_eq (by ring); rw [LidFee,pow_two]; have ht : (W:ℝ)≤((u:ℝ)+3):=by exact_mod_cast hw
        gcongr
end YM.OPE.Variance
