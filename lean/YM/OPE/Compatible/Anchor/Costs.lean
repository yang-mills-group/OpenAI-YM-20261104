import YM.OPE.Compatible.Anchor.Cyst
/-! # angular exposure.Valuation.Top -/
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
local notation "θ"=> 𝓝[>] (0:ℝ)
local notation "C!" => fieldX (Shade G)
variable {K:Sponsor G}{T:Seasons K}{v:ℝ}
variable (A:Alps K T i v)
lemma wageScale (c:ℝ)(x:C!)(a:Axis)(w:Cover)(p:Fin j→ Axis): wageZ A p (c • x) a w=c • wageZ A p x a w:=by
     unfold wageZ; rw [show (fun y:Cover=>rootζ A (c • x) (y,a))=c • (fun y:Cover=>rootζ A x (y,a)) from ?_,map_smul,Pi.smul_apply]; funext z; ext i; let T:= barrage (pink K.K.penalty A.gear); change meetsX T (shadew i (c • x)) (z,coord a)=c*meetsX T (shadew i x) (z,coord a); unfold meetsX;rw [← tsum_mul_left]; refine tsum_congr fun i=>?_ ; exact mul_left_comm ..
lemma wageAdd (x y:C!)(hp:Quiet x d)(hr:Quiet y d)(hs:4 ≤ i)(a: Axis)(w:Cover)(p:Fin j→Axis): wageZ A p (x+y) a w=wageZ A p x a w+wageZ A p y a w:=by
     let f(z:C!)(x:Cover):= rootζ A z (x,a); unfold wageZ; rw[show (fun y'=>_) = f x+f y from ?_,map_add,Pi.add_apply]
     let T:=barrage (pink K.K.penalty A.gear); have he:Whole T:= barrageH ((heart_saves K.K.penalty K.K.penalty_pos hs (fun i:Train i=>i)).1.whole _); ext1 v; ext1 i; change meetsX T (shadew _ (x+y)) (v,coord a)= _; let z:=(v,coord a); unfold meetsX; change (∑' j,T _ _ _ * _)= meetsX T (shadew i x) z+meetsX T (shadew i y) z; unfold meetsX; rw [← Summable.tsum_add (show Summable _ from meets_current (J:=_) he (quietShade hp i) v (coord a)) (meets_current he (quietShade hr i) v (coord a))]; refine tsum_congr fun k=>?_ ; exact mul_add ..
lemma wave_blend (f:I→ fieldX (Shade G))(hp:∀ i,Quiet (f i) d)(p:Fin j→Axis)(a:Axis)(w: Cover)(S: Finset I)(hs:4 ≤ i):
    wageZ A p (∑ i∈S, f i) a w=∑ i∈S,wageZ A p (f i) a w:=by induction S using Finset.induction_on with
     | empty=> simp only [Finset.sum_empty]; let h:=wageScale A 0 (showerW 0 0 0) a w p; simpa using h
     | insert i S hi ih=>
       rw [sum_insert hi,sum_insert hi,wageAdd A _ _ (hp i) _ hs,ih]; clear hi ih; induction S using Finset.induction_on with
       | empty=> simp only[sum_empty]; exact ⟨0,le_rfl,fun i=>by erw [Pi.zero_apply,norm_zero, zero_mul]⟩
       | insert i s hi ih=> rw [sum_insert hi]; exact quietAdd (hp i) ih
lemma taperΞ {G:Gauge} (v:Taylor G k)(h:k=l): jetΦ G k v=jetΦ G l (h ▸ v):=by subst k; rfl
lemma flareM {A:Alps K T i v} (hs:4 ≤ i)(v:Alphabet G d)(g:Fin d)(h:g.val=j+1)(p:Fin j→Axis)(w:Cover)(a:Axis)(X:Taylor G (j+1))(hX:h ▸ v g=X) :
     BillUp G.Color (j+2) (fun t=>wageZ A p (showerW d t v) a w) (- ((j+1).factorial:ℝ) • flame X a (basis ∘ p)):=by
       subst X; let f(k:Fin d):=wageZ A p (jetΦ G _ (v k)) a w; let y(k:Fin d)(t:ℝ):=t^(k.val+1) • f k; let u(k:Fin d):=if h:j+2=k.val+1 then f k else 0
       rw [show (fun t=>wageZ A p (showerW d t v) a w)=(fun t=> ∑ k,y k t) from ?_]; swap
       · funext t; rw [showerW,LinearMap.sum_apply,wave_blend A _ (d:=d) _ _ _ _ _ hs]; apply sum_congr rfl; intro i _; exact wageScale A _ _ a w p; intro i; exact quiet_up (by change Quiet ((_ :ℝ) • jetΦ G _ (v _)) (i.val+1); rw [← _root_.map_smul]; exact low_quiet (ledgeL (t^(i.val+1) • v i).val)) i.isLt -- implicit q
       suffices H: (∑ i: Fin d,u i)= - ((j+1).factorial:ℝ) • flame (h ▸ v g) a (basis ∘ p) by
          rw [← H]; apply UpLayer univ y u; intro k hk; by_cases hh:j+2 ≤ k.val+1; · exact UpPrice _ hh
          rw [show u k =0 from dif_neg (by omega)]; rw [show y k=fun (_:ℝ)=>0 from funext fun t=>by unfold y f; rw [BlankΩ A hs p a _ w (by omega),smul_zero]]; unfold BillUp; simp
       rw [sum_eq_single g]; · rw [show u g =f g from dif_pos (by omega)]; rw [show f g=wageZ A p (jetΦ G (j+1) (h ▸ v g)) a w from ?_,ΩCapital A hs]; congr! 1; exact taperΞ (v g) _
       · intro i _ hi; unfold u; rw [dif_neg fun e=>hi (Fin.ext (by omega))]
       simp
end YM.OPE.Variance
