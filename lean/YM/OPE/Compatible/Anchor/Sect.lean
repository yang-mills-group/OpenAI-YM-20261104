import YM.OPE.Compatible.Anchor.Herd
/-!
# Generator angular vector tensors.Lift operation. Gen.H matrix independent before layers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
variable {K:Sponsor G}{S:Seasons K}{u:M→ℝ}{v:ℝ}{τ:Phase→ℕ}
local notation "Ξ"=>solar G d τ
local notation "θ"=> 𝓝[>] (0:ℝ)
variable (L:M→Submodule ℝ (solar G d τ))(A:(j:M)→Alps K S i (u j)){α:Fin r→Fin k}(Fθ:SpiceK G α)
lemma DotCL (u v:G.Color)(x:ℝ): Dotty (x • u) v=x*Dotty u v:=by unfold Dotty; rw [mul_sum]; apply sum_congr rfl; intro i _; change x*u i*v i=_; ring
lemma wageDot (B:Fin j→Axis)(a:Axis)(p:Cover) (he:r+1≤d)(hp:(r+1)*k≤τ 0) (hv:G.Simple)(hf:Abalo Fθ)(h:Forum A L):
     RoomN (ZTheta u) L (fun t x=>Dotty (wageZ (A t) B x a p) (ClearW Fθ x)) (r+1) k:=by
       obtain ⟨s,c,H⟩:=train_s B p; let f(y:Cover)(t:M)(x:fieldX (Shade G)) := Dotty (rootζ (A t) x (y,a)) (ClearW Fθ x); let g(i):= c i • f i; rw [show (fun (t:M) x=> Dotty (wageZ (A t) B x a p) (ClearW Fθ x))=∑ i∈s,g i from ?_]; exact RoomN.sum L s g (fun i _=> RoomN.smul L (farm_s L A Fθ (i,a) he hp hv hf h) (c i)) hp
       funext t x; rw[Finset.sum_apply,Finset.sum_apply]; unfold Dotty; let v(y:Cover):= rootζ (A t) x (y,a); let z:=trainX G.Color j B v; have he (i:G.ColorIndex):z p i= ∑ y∈s,c y*v y i:=by let f:= chin i; change (f ∘ z) p=_; unfold z; erw [← tracksX f.toLinearMap,H]; rfl
       change (∑ i,z p i*_)=_; simp_rw [he, sum_mul]; rw[sum_comm]; refine sum_congr rfl fun j _=>?_ ; change (∑ i,c j*v j i*_)= c j * _; unfold f Dotty; rw [mul_sum]; apply sum_congr rfl; intro i _;change _=c _* (v _ _*_); ring
noncomputable abbrev χFlat (w:Axis)(B:Fin j→Axis)(g:Fin k)(hg:g.val=j+1)(x:Alphabet G k):= Dotty (flame (hg ▸ x g) w (basis ∘ B)) (Fθ (fun i=> x (α i)))
lemma renewZ (w:Axis)(B:Fin j→Axis)(g:Fin k)(hg:g.val=j+1)(hp:(r+1)*k ≤ τ 0)(he:r+1≤d)(hv:G.Simple)(hf:Abalo Fθ) (h:Forum A L) :
    Obtains (ZTheta u) L (r+1) (j+2+rankX α) (χFlat Fθ w B g hg):=by
       let c:ℝ:= -((j+1).factorial:ℝ); have hc:c≠0:= by unfold c; rw [neg_ne_zero];exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
       have hV : Obtains _ L (r+1) (j+2+rankX α) (c • χFlat Fθ w B g hg):= RoomN.get L (R:= c • χFlat Fθ w B g hg) (wageDot L A Fθ B w 0 he hp hv hf h) (fun i x=>?_ ) -- target BillUp

       · rw [← inv_smul_smul₀ hc (χFlat Fθ w B g hg)]; exact Obtains.smul L hV _
       have ht:= cueD A Fθ w B x g hg 0 (hg ▸ x g) rfl h.enough i; rw [DotCL] at ht; exact ht
end YM.OPE.Variance
