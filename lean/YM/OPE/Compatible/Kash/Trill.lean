import YM.OPE.Compatible.Kash.Gusto
import YM.OPE.Compatible.Kash.Lease
import YM.OPE.Compatible.Kash.Sump
import YM.OPE.Compatible.Glim.Xpand
/-! # Uniform supplies of finite-angular scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d k m r l:ℕ}{Z I J:Type}
variable {n:Side}{x t:ℝ}
local notation "C!"=> Curtain (Shade G)
local notation "Φ" n:arg=>Bid.Dir G n
variable [Fintype I]
variable (F:Libra.Keys G I→ℝ)(h:ContDiffAt ℝ ω F 0)
abbrev Wallet (F:Libra.Keys G I→ℝ) (k:ℕ)(c:ℝ) := ∀ x:Fin k→ Libra.Keys G I,(∀ i, ‖x i‖ ≤ 1)→ ‖(Tensor.coeff F k 0) x‖≤ c
variable (k b m:ℕ)(T:I→RootEdge){c:ℝ}(ht:∀ i,(1+size (T i).1)^m ≤ b)
noncomputable abbrev grainS (T:Type) [Fintype T](b k:ℕ)(c:ℝ):ℝ:= grain c (Fintype.card T) b k
include h
lemma ΔJet (n:Side)(x:Site n): jet (F ∘ dip T n x) k= Tensor.diagonal (Tensor.coeff F k 0) ∘ (dip T n x):= by
      funext v; exact (congr_arg JetS.s (congr_fun (moldC (dip T _ _) F h k) v)) -- orientation
include ht
lemma Twins (hx: Wallet F k c) : UnitL (grainS (I×G.ColorIndex) b k c) (fun n x=>jet (F∘ dip T n x) k) k m:= (monaC _ m b T ht hx).congrZ (Eventually.of_forall fun n=> funext fun x=>(ΔJet F h k T n x).symm)
lemma Picks (hx:Wallet F (k+1) c)(e:RootEdge)(u:G.ColorIndex):UnitL (‖((k:ℝ)+1)‖*grainS (I×G.ColorIndex) b k c) (fun n x v=> fderiv ℝ (jet (F∘dip T n x) (k+1)) v (functorE x e u)) k m:=by
       obtain ⟨v,hv⟩:=hump e u T; have ht': ‖v‖ ≤ 1 :=by
          obtain ⟨x,hx⟩:=hv.exists; rw[← hx 0]; let R:= (sett x (0:Site x) e); exact (pi_norm_le_iff_of_nonneg (zero_le_one)).mpr fun i=> le_trans (norm_le_pi_norm (functorE (0:Site x) e u) (sett x 0 (T i))) (show ‖An R (Phone G) u‖≤1 from paw (R,u))
       let P:=Tensor.coeff F (k+1) 0; have hp:Tensor.Sym P:=Tensor.coeff_symm (h.of_le le_top); let S:=P.curryLeft v; have he :∀ x:Fin k→Libra.Keys G I,(∀ i, ‖x i‖≤1)→ ‖S x‖ ≤ c :=fun x hh=> hx (Fin.cons v x) (fun i=>by refine Fin.cases ?_ ?_ i; rwa[Fin.cons_zero]; exact fun i=>by rw[Fin.cons_succ]; exact hh i)
       refine (UnitL.color (k+1:ℝ) (monaC S m b T ht he)).congrZ (hv.mono (fun n hi=>?_)); funext x w; let y:= dip T n x (G:=G); have hQ : DifferentiableAt ℝ (Tensor.diagonal P) (y w):=(Tensor.diag_smooth _ ω).differentiable (by simp) _; change _= fderiv ℝ (jet (F∘ y) _) w _; rw [show jet (F∘ y) _ =_ from ΔJet F h (k+1) T n x, fderiv_comp w hQ y.differentiableAt,y.fderiv,ContinuousLinearMap.comp_apply,(hi x),Tensor.differential_diagonal _ hp,← Nat.cast_smul_eq_nsmul ℝ]; push_cast;rfl -- y definitional
end YM.OPE.Variance
