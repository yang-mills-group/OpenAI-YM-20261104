import YM.OPE.Compatible.Anchor.Rune
/-!
# Rank ruler.H phase 0 motion
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J W M:Type}{n:Side}{K:Sponsor G}{T:Seasons K}{u:ℝ}
variable {e:RootEdge}
local notation "Y!" => Bid.Dir G n
local notation "B"=> Phone G
lemma rootRead (f:Alps K T i u)(hp:i≥4)(p:fieldX (Shade G))(y:ℕ)(_hq: Quiet p y)(a:G.ColorIndex) (t:W→Side) {φ:Filter W} -- W implicit add
    (v:∀ i:W,Bid.Dir G (t i))(hx:Realized t φ p (fun i=> spool G _ (v i)) y):
    Tendsto (fun i:W=> bat (functorE (0:Site (t i)) e a) (jet (Dune f) 2) (v i)) φ (𝓝 (meetsX (barrage (pink K.K.penalty f.gear)) (shadew a p) (e.1,coord e.2))):=by
       let R:= pink K.K.penalty f.gear; let u(i:W) := parts G 1 (v i) a
       have hg: Realized t φ (shadew a p) u y:=by
            have he(x:Cover)(j:Axis)(p:fieldX (Shade G)): shadew a p (x,axisEquiv j)=p (x,j,a):=by simp only [shadew,Equiv.symm_apply_apply]
            constructor
            · obtain ⟨d,hD,H⟩:=hx.Once; refine ⟨_,hD,fun i j=>?_⟩; obtain ⟨x,j⟩:=j; obtain ⟨z,rfl⟩:=axisEquiv.surjective j; exact H i (x,z,a)
            intro j; obtain ⟨x,j⟩:=j; obtain ⟨z,rfl⟩:=axisEquiv.surjective j; rw [he]; exact hx.Onset (x,z,a)
       have hr:Whole R:=(heart_saves K.K.penalty K.K.penalty_pos hp (fun i:Train i=>i)).1.whole f.gear; have he:= (meetings hg (barrageH hr)).Onset (e.1,coord e.2); refine he.congr (fun j=>?_); rw[lance_i f hp];change ((barrage R).acts _ *ᵥ u j) _ =_; rw [show sett (t j) 0 e=(wrap _ e.1,coord e.2) from (by unfold sett whiz placed; rw[zero_add]; rfl),show (barrage R).acts (t j)=f.root.acts (t j) from ?_]
       have hQ:=Whole.boundary 1; rw [Alps.root,Woody.Op_stays hp, barrage,hQ.flipped.acts (hr.prod hQ),hr.acts hQ,acts_trans,← Matrix.mul_assoc];rfl -- Op unfolds
open Polynomial
section
variable {A:foliage G}{τ:Phase→ℕ}
noncomputable abbrev topX (X:solar G d τ):Curtain (Shade G):= spread G d τ X.val 0
abbrev CapE (i:ℕ)(X:solar G d τ): Prop:=∀ j>i,topX X j=0
lemma budget_φ {V:solar G d τ}{P:Polynomial ℝ}(hp:mind V.val n 0=A n 0)(v:Bid.Dir G n)(hv:∀ x:ℝ,Polynomial.eval x P=(A n 0 (x • v)).s) : Flume.Script.value 0 (topX V j) (spool G n v)= if j≤d then P.coeff j else 0:=top_rank A V n 0 v P hp hv _
lemma Chip {V:solar G d τ}{p:Libra.Keys G (Body 1 n)→ G.Color}{f g:Y!→ℝ}(h:A n 0 = Cake (sett n 0 e) false f g p r)(hp:mind V.val n 0=A n 0)(hv:ContDiffAt ℝ ω f 0)(ht:ContDiffAt ℝ ω p 0)(hr:r+1≤ d)(v:Bid.Dir G n):
    Flume.Script.value 0 (topX V (r+1)) (spool G n v)=topψ (sett n 0 e) r f p v∧∀ j>r+1,Flume.Script.value 0 (topX V j) (spool G n v)=0:=by
       let a:= sett n 0 e; let T:=topψ a r f p v; let Q:=botψ a r p v; let P:= Polynomial.monomial (r+1) T+Polynomial.monomial (r-1) Q; have he(x:ℝ): P.eval x=(A _ 0 (x • v)).s:= by rw [show A _ _= _ from h,speedCake _ _ _ v p r x hv ht]; unfold P; rw[eval_add,eval_monomial,eval_monomial]; unfold T Q a; ring
       have hk:r-1<r+1:=by omega
       constructor; · rw [budget_φ hp v he,if_pos hr]; unfold P;rw[coeff_add,coeff_monomial,if_pos rfl,coeff_monomial,if_neg (by omega),add_zero]
       intro j hj; rw[budget_φ hp v he];split; next h=> unfold P;rw[coeff_add,coeff_monomial,if_neg (by omega),coeff_monomial,if_neg (by omega),zero_add]
       rfl
end
end YM.OPE.Variance
