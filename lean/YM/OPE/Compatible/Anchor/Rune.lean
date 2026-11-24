import YM.OPE.Compatible.Anchor.Rain
/-! # unwrapped forcing. True strip, startup.X.R matrix -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent Work.F05
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M:Type}{n:Side}{K:Sponsor G}{T:Seasons K}{u:ℝ}
variable {e:RootEdge}(f:Alps K T i u) (hi:4 ≤ i)
local notation "Y" => Bid.Dir G n
local notation "B"=> Phone G
include hi
lemma S32 (z w:Y):iteratedFDeriv ℝ 2 (Dune f (n:=n)) 0 ![z,w]= dotProduct (flatten z) (tensor G (f.root.acts n) *ᵥ flatten w):=by
   unfold Dune; rw [iteratedFDeriv_sub_apply (show ContDiffAt ℝ _ (frameD f (n:=n)) _ from ((f.fullK 1).plot _).of_le le_top) contDiffAt_const,iteratedFDeriv_const_of_ne (by decide),Pi.zero_apply,sub_zero]; exact f.inkTot hi ..
lemma lance_i (x:Site n)(a:G.ColorIndex)(v:Bid.Dir G n): bat (functorE x e a) (jet (Dune f) 2) v = (f.root.acts n *ᵥ parts G 1 v a) (sett n x e):=by
   let q:= functorE x e a; let P:= Dune f (n:=n); let C:=iteratedFDeriv ℝ 2 P 0; have hp: ContDiffAt ℝ ω P 0 := ((f.fullK 1).plot _).sub contDiffAt_const
   have he: bat q (jet P 2) v= dotProduct (flatten q) (tensor G (f.root.acts n) *ᵥ flatten v):=by
        unfold bat; change fderiv ℝ (Tensor.diagonal (Tensor.coeff P 2 0)) v q= _; rw [Tensor.differential_diagonal _ (Tensor.coeff_symm (hp.of_le le_top))]; rw [← S32 f hi]; unfold Tensor.coeff; simp only[ContinuousMultilinearMap.curryLeft_apply,_root_.smul_apply]; rw [show Fin.cons q (fun _:Fin 1=>v)=![q,v] from funext fun i=>by fin_cases i<;>rfl]; rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]; norm_num [P]
   rw [he]; let b:=bench n x e a; have hv: flatten q=deltaH (lent G n b):=by rw [show q=(spool G n).symm (deltaH b) from ?_]; exact Alps.delta_lent _; rw [show (deltaH b)=spool G n q from (topHere ..).symm,(spool ..).symm_apply_apply]
   rw [hv]; let W:=tensor G (f.root.acts n) *ᵥ flatten v; let L:=lent G n b; have hh: dotProduct (deltaH L) W=W L:=by simp [deltaH]
   rw [hh]; let z:=sett n x e; have hz: L=(z.1,z.2,a):=rfl; rw [hz]; exact congr_fun (component_mul (f.root.acts n) (flatten v) a) z -- direction maybe hv
end YM.OPE.Variance
