import YM.OPE.Compatible.Glim.Zeno
/-! # VolForce budget -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J:Type}{n:Side}
variable (e:RootEdge)(u:G.ColorIndex)
lemma Need (p:Script (Shade G) (r+1))(h:Summable p)(f:Bid.Dir G n→ℝ) (hp:ContDiffAt ℝ ω f 0) (ht:∀ v:Fin (r+1)→Bid.Dir G n,library n p (spool G n ∘ v)=iteratedFDeriv ℝ (r+1) f 0 v)(x:Site n)(v: Bid.Dir G n):
     fderiv ℝ (jet f (r+1)) v (functorE x e u) = ((r+1:ℕ):ℝ)* ((r+1).factorial:ℝ)⁻¹ *Flume.Script.value x (cotton (unitRow _) (r:=0) (punch e u) p) (spool G n v):=by
     let K:= Tensor.coeff f (r+1) 0; change fderiv ℝ (Tensor.diagonal K) v _=_; rw [Tensor.differential_diagonal K (Tensor.coeff_symm (hp.of_le le_top)), ← Nat.cast_smul_eq_nsmul ℝ,smul_eq_mul, ← DrawRead p h x e u v, ht,mul_assoc];rfl
lemma NeedV {P:Z→ Script (Shade G) (r+1)}{v:Z→ℝ}{z:Z→(n:Side)→Bid.Dir G n→ℝ}(c:ℝ)(hc:0≤c)(hp:∀ t,soot m (P t) (c*v t))(hv:∀ i n,ContDiffAt ℝ ω (z i n) 0)(h:∀ i n q,library n (P i) (spool G n ∘ q)=iteratedFDeriv ℝ (r+1) (z i n) 0 q): Take v (fun i n x a=> fderiv ℝ (jet (z i n) (r+1)) a (functorE x e u)) r m:=by
     let p:= punch e u; let f(i:Z):= cotton (unitRow _) (r:=0) p (P i); let s:= figure m (fun _:Fin 1=> (e.1,e.2,u)); let b:=s*c*(widthCost 1 m)*((3*r+2:ℕ):ℝ)^m; have he : 0 ≤ s:=zero_le_one.trans (payer ..); have h₁:0 ≤ widthCost 1 m:= zero_le_one.trans (widthCost_ge one_pos m); have hX(i:Z):soot m (f i) (b*v i):= by
          refine (cotton_cost (A:=unitRow _) (s:=1) (U:=1) (fun _ _=> Work.F08.strip_unit ..) one_pos zero_le_one (bread e u m) (hp i)).tips (le_of_eq ?_); unfold b s;ring
     let d:ℝ:= ((r+1:ℕ):ℝ) *((r+1).factorial:ℝ)⁻¹; have ht:=Take.bead f b (by unfold b; positivity) hX; refine Take.raise (Take.congr (Take.scale ht d) ?_) le_rfl (by omega); intro i; filter_upwards with n; funext x a; exact (Need e u (P i) (sootS (hp i)) (z i n) (hv i n) (h i n) x a).symm
end YM.OPE.Variance
