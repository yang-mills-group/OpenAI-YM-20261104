import YM.OPE.Compatible.Song.Get
/-!
# Glue and split for unconditional Warranty.Layer alpha+
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL
variable {i j d k m r l b:ℕ}{n:Side}
variable {I W:Type} {B:I→ Finset (Edge Cover)}{N:I→ Side}{φ:Filter I}{Z:I→ℝ}
variable {M:I→ℕ}(A:Audience φ Z N M r)
variable {p q z:Forge G N}{s:Phase}
lemma gapV.sum (h:gapV p k φ) (h':gapV q k φ):gapV (p+q) k φ:= by intro i hi; filter_upwards [h _ hi,h' _ hi] with j hj he; rw [eye_add,Pi.add_apply,hj,he,add_zero]
lemma gapV.sub (h:gapV p k φ) (h':gapV q k φ):gapV (p-q) k φ:= by intro i hi; filter_upwards [h _ hi,h' _ hi] with j hj he; rw [eye_sub,Pi.sub_apply,hj,he,sub_zero]
lemma Pulse (Q:Forge G N)(s:Phase):gapV (LiftA s Q) s.val φ:=fun _ hi=>Eventually.of_forall fun j=> congr_fun (early s _ Q hi) j
lemma lapse (h:gapV p s.val φ)(hh: ∀ᶠ i in φ, eyeR p s i=0): gapV p (s.val+1) φ:=by
       intro t ht; by_cases he:t.val=s.val; · rw[show t=s from Fin.ext he]; exact hh
       exact h _ (by omega)
lemma gapV.null (h:gapV p 3 φ):∀ᶠ i in φ,p i=0:=by
       filter_upwards [h 0 (by decide),h 1 (by decide),h 2 (by decide)] with i hi hx hp
       exact funext fun j=>JetS.eta _ _ (congr_fun hi j) (congr_fun hx j) (congr_fun hp j)
lemma SubL {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (p q:E→ℝ)(hp:ContDiff ℝ ω p)(hq:ContDiff ℝ ω q)(k:ℕ): Claw.rank (p-q) k=Claw.rank p k - Claw.rank q k:=by
       rw [sub_eq_add_neg]; unfold Claw.rank;rw [Tensor.coeff_add (g:=-q) (hp.of_le le_top|>.contDiffAt) ((hq.of_le le_top|>.contDiffAt).neg),Tensor.neg_coeff]; funext x; rw [sub_eq_add_neg]; rfl -- likely sub not defeq
lemma whirl (ht:Tendsto Z φ atTop)
     (h:Filμ B φ Z (eyeR p s) (k+1))(h':Filμ B φ Z (eyeR q s) (k+1)) (h₂:Filμ B φ Z (eyeR z s) (k+1))
     (hg:∀ᶠ i in φ, Claw.rank (eyeR p s i) (k+1)-Claw.rank (eyeR q s i) (k+1)=Claw.rank (eyeR z s i) (k+1)): Filμ B φ Z (eyeR (p-q-z) s) k:=by
        rw[eye_sub,eye_sub]; refine lowerV ((h.minus ht h').minus ht h₂) ?_; filter_upwards [h.tariff,h'.tariff,h₂.tariff,hg] with i hp ht hx hk; rw [Pi.sub_apply,Pi.sub_apply,SubL _ _ (Tall.neat (Tall.bite hp ht)) hx.neat, SubL _ _ hp.neat ht.neat, hk,sub_self]
end YM.OPE.Merchant
