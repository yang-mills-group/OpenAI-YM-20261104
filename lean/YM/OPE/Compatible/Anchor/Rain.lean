import YM.OPE.Compatible.Anchor.Rise
/-! # rank: untouched top coefficient.Wick -/
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
variable {i j d k m r l:ℕ}{Z I J M:Type}{n:Side}
variable [Fintype I](p:I)(x y:G.ColorIndex)
local notation "E!"=> Libra.Keys G I
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
omit [Fintype I] in lemma relic (i:ℕ)(v:E)(f:E→ℝ)(t:ℝ):jet f i (t • v)=t^i *jet f i v:= Tensor.homogeneous (Tensor.coeff f i 0) v t
omit [Fintype I] in lemma rerun (i:ℕ)(f:E→ℝ)(x v:E)(hp:ContDiffAt ℝ ω f 0)(t:ℝ): bat x (jet f i) (t • v)= t^(i-1)*bat x (jet f i) v:=by
    cases i; · unfold bat; rw [show jet f 0=fun _=>f 0 from funext fun i=>jet_zero .., fderiv_const_apply,fderiv_const_apply]; change (0:ℝ)=_*0; rw[mul_zero]
    unfold bat; rw [vast _ _ hp,vast _ _ hp,relic]; rfl -- succ
local notation "U"=> G.Color
noncomputable def topψ (r:ℕ)(f:E!→ℝ)(Y:E!→G.Color)(v:E!):ℝ:=∑ i:G.ColorIndex, bat (An p (Phone G) i) (jet f 2) v * jet ((Phone G).coord i∘Y) r v
noncomputable abbrev botψ (r:ℕ)(Y:E!→G.Color)(v:E!):ℝ:= ∑ i:G.ColorIndex,-bat (An p (Phone G) i) (jet ((Phone G).coord i ∘ Y) r) v
lemma speedCake (f g:E!→ℝ)(v:E!)(Y:E!→G.Color)(r:ℕ)(t:ℝ)(hp:ContDiffAt ℝ ω f 0)(hY:ContDiffAt ℝ ω Y 0): (Cake p false f g Y r (t • v)).s=t^(r+1) * topψ p r f Y v+ t^(r-1)*botψ p r Y v:=by
     rw [Duke]; unfold topψ botψ; rw [mul_sum,mul_sum,←sum_add_distrib]; refine sum_congr rfl (fun i _=> ?_); let C:=((Phone G).coord i); let x:=C∘ Y; have hf:ContDiffAt ℝ ω x 0:=C.toContinuousLinearMap.contDiff.contDiffAt.comp _ hY
     dsimp only; rw [rerun _ f _ _ hp, show bat _ _ _= _ from (show bat (An p (Phone G) i) (jet x r) (t • v)=_ from rerun r x _ _ hf t), relic]; change t^1 * _ * _ - _= _; unfold x C; ring
open Polynomial
omit [Fintype I] in lemma top_rank {τ:Phase→ℕ} (A:foliage G)(X:solar G d τ) -- fix binder
       (n:Side)(x:Site n)(v:Bid.Dir G n)(P:Polynomial ℝ)(hp:mind X.val n x=A n x)(h:∀ s:ℝ,Polynomial.eval s P=(A n x (s • v)).s)(j:ℕ):
    Flume.Script.value x ((spread G d τ X.val) 0 j) (spool G n v)= if j≤d then P.coeff j else 0:=by
       let Q:= spread G d τ X.val; let f:=spool G n v; let W:=Q 0; have hv(s:ℝ): Flair W d (s • f) x=Polynomial.eval s P:=by
            rw [h,← hp]; change Flair W d _ _=Flair W _ (spool G n (s • v)) x; rw [map_smul];rfl
       let T:= ∑ i∈range (d+1), Polynomial.monomial i (Flume.Script.value x (W i) f); have ht:P=T:=Polynomial.funext fun i=> (hv i).symm.trans (Grid.rollPoly ..); rw [ht];by_cases he:j≤d
       · rw [if_pos he]; unfold T;rw [finsetSum_coeff,sum_eq_single j,coeff_monomial]; simp [W,Q,f]; intro i _ hi; simp [coeff_monomial,hi]; intro hz; exact False.elim (hz (mem_range.mpr (by omega)))
       rw [if_neg he, ((resin (d:=d) X.val (m:=0) (fun _=>Nat.zero_le _)) 0).1 j (by change d+0 < j; omega)]; simp [Flume.Script.value, scribe]
-- Φ∀ exposes ANY code
end YM.OPE.Variance
