import YM.OPE.Compatible.Wells.Lac
/-!
# Genuine chamber innovation charges. Complete Ward representation on translated restricted plane.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Coin
variable {i j d k m r l b:ℕ}{n:Side}
variable (hp:Board n (r+1))
variable {P:ChartRatio G} (hr:LocalRatio P)(u:G.Color)
variable (L:Law (Chamber G r))(x:Bid.Dir G n) (q:↥(fieldP r))
local notation "T!"=> Chamber G r
local notation "R!"=> sailT G hp
local notation "t!"=>turn (sailT G hp) x
noncomputable abbrev ΓJac (P:ChartRatio G)(x:Bid.Dir G n) :ScriptJ (Chamber G r):= (Pawn.mold (Chart.jacobian P) 0) ∘ R_τ x
-- charges
variable (f g:Bid.Dir G n→ℝ)
noncomputable abbrev ΓLog:= BookW f g ∘ turn (sailT G hp) x
noncomputable abbrev ΓWeight (P:ChartRatio G)(z:Token):= (fun _:Chamber G r=>z)*ΓJac (r:=r) P x * wheel (ΓLog hp x f g)
local notation "p!"=>ΓLog hp x f g
section
lemma JacBond : ScriptJ.B (ΓJac P x (r:=r)):= turnB _ (PinT G x) _ (tallJ _ _)
lemma LogBond : ScriptJ.B (p!):= turnB _ x _ (ScriptJ.key (tallJ _ _) (tallJ _ _))
lemma WeightB (z:Token): ScriptJ.B (ΓWeight hp x f g P z):=height (height (Bfray z) (turnB _ (PinT G x) _ (tallJ _ _))) (heightens (p!) (LogBond hp x f g))
lemma Logζ (c:ℝ)(h:∀ y,jet f 2 (turn (sailT G hp) x y) = L.P y y/2 + c) (b:T!): spur (Pry b (p!))= Variance.link L b:=by
       let p:=p!; let t(i:T!):=(p i).s; let v(i:T!):= L.P i i/2; let d:=c+g 0; have he: t=v+fun _=>d:=funext fun y=> (by change jet f 2 _+jet g 0 _=_; rw[h,jet_zero]; unfold v d; simp only [Pi.add_apply,add_assoc]); funext y; apply JetS.eta
       · have hz:DifferentiableAt ℝ v y:=by unfold v; simp_rw[div_eq_mul_inv]; exact (((Libra.Pose.standE L).smooth.differentiable (by simp)) y).mul_const _
         change fderiv ℝ t y b=L.P b y; rw [he, fderiv_add hz (differentiableAt_const _),fderiv_const_apply,add_zero]; exact billing L y b -- v line
       · rfl
       rfl
variable (μ:Measure (Chamber G r))[μ.IsAddHaarMeasure]
include hr
local notation "Y!"=> Mount (sett n 0 q.val)
omit hr in private lemma liftedL {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F] (R:E→L[ℝ] F)(x:F)(u:I→E)(v:I→F)(Y:I→ScriptJ F)(H:Finset I)(f g:ScriptJ F)(h:(fun i=>R (u i))=v)(hf:f.B)(hp:g.B): Stamp v Y H f g ∘ turn R x=Stamp u (fun i=>Y i∘turn R x) H (f∘turn R x) (g∘turn R x):=by unfold Stamp; rw [turnZ R x u Y H f hf,turnZ R x u Y H g hp,h]; rfl
noncomputable abbrev Act (u:G.Color)(x:Bid.Dir G n)(j:G.ColorIndex):= Mount (sett n 0 q.val) u false j ∘ (turn (sailT G hp) x)
omit hr in set_option maxHeartbeats 200000 in lemma LoopGen (i:G.ColorIndex): sailT G hp (An q (Phone G) i)=An (sett n 0 q.val) (Phone G) i:=ferryT G hp q i
omit hr in set_option maxHeartbeats 200000 in private lemma Sprink (G':ScriptJ (Bid.Dir G n))(hG:G'.B) (F:ScriptJ (Bid.Dir G n))(hx:F.B): Stamp (E:=Bid.Dir G n) (An (sett n 0 q.val) (Phone G)) (Mount (sett n 0 q.val) u false) univ G' F ∘ turn (E:=Chamber G r) (F:=Bid.Dir G n) (sailT G hp) x = Stamp (E:=Chamber G r) (An q (Phone G)) (fun i=> (@Function.comp (Chamber G r) (Bid.Dir G n) Token (Mount (sett n 0 q.val) u false i) (turn (sailT G hp) x))) univ (G' ∘ t!) (F ∘ t!):=by
        let R:= sailT G hp; let P:=An (sett n 0 q.val) (Phone G); let f:= Mount (sett n 0 q.val) u false; let K:= An q (Phone G)
        have he: (fun i=> R (K i))=P :=by
             unfold P K R; exact funext fun i=> LoopGen hp q i
        have hz:= liftedL (E:=Chamber G r) (F:=Bid.Dir G n) R x K P f univ G' F he hG hx
        -- proof
        change @Eq (ScriptJ (Chamber G r)) _ _; with_reducible_and_instances exact hz
lemma Sprig (c:ℝ)(h:∀ y,jet f 2 (turn (sailT G hp) x y)= L.P y y/2+c)(z:Token)(F:ScriptJ T!)(hx:F.B): draw (ΓWeight hp x f g P z * Stamp (E:=Chamber G r) (An q (Phone G)) (Act hp q u x) univ (p!) F) L μ=0:=by
  let K : G.ColorIndex → Chamber G r := An q (Phone G)
  let Y : G.ColorIndex → ScriptJ (Chamber G r) := Act hp q u x
  let j : ScriptJ (Chamber G r) := ΓJac P x
  let a : ScriptJ (Chamber G r) := p!
  have yb (i:G.ColorIndex) : (Y i).B := by
    with_reducible_and_instances exact turnB (sailT G hp) x _ (tallJ _ _)
  have affine (i:G.ColorIndex) : spur (Pry (K i) a)=Variance.link L (K i):=Logζ hp L x f g c h (K i)
  have trace : divergence K Y univ*j+Flux K Y univ j=0:=by
    with_reducible_and_instances exact τPit hp hr u x q
  have result:=ere K univ L Y j a μ (fun i _=>yb i) z F hx
    (JacBond (r:=r) x) (LogBond hp x f g) affine trace
  with_reducible_and_instances exact result
set_option maxHeartbeats 200000 in
lemma mintΓ (c:ℝ)(h:∀ y,jet f 2 (turn (sailT G hp) x y)= L.P y y/2+c)(z:Token)(F:ScriptJ (Bid.Dir G n))(hx:F.B):
       let W:=ΓWeight hp x f g P z; let S:= Stamp (E:=Bid.Dir G n) (An (sett n 0 q.val) (Phone G)) (Mount (sett n 0 q.val) u false) univ (BookW f g) F
       draw (W*(S ∘ (turn (sailT G hp) x))) L μ=0:=by
           intro W S; have he:=Sprig hp hr u L x q f g μ c h z (F ∘ t!) (turnB _ _ _ hx)
           have hG: ScriptJ.B (BookW f g):=ScriptJ.key (tallJ _ _) (tallJ _ _); have hz:= Sprink hp u x q (BookW f g) hG F hx; have hZ:(S ∘ t!)=Stamp (E:=Chamber G r) (An q (Phone G)) (Act hp q u x) univ (p!) (F ∘ t!):=by with_reducible_and_instances exact hz
           with_reducible_and_instances exact Eq.trans (congr_arg (fun (f:ScriptJ (Chamber G r))=>draw (W*f) L μ) hZ) he
lemma ΓCake (c:ℝ)(h:∀ y,jet f 2 (turn (sailT G hp) x y)= L.P y y/2+c)(z:Token)(Y:Bid.Dir G n→G.Color):
       let W:=ΓWeight hp x f g P z; let S:= Cake (sett n 0 q.val) false f g Y k
       draw (W*(S ∘ (turn (sailT G hp) x))) L μ=0:=by
         let i:= sett n 0 q.val; let fj(j:G.ColorIndex):= Pawn.mold ((Phone G).coord j ∘ Y) k; let a(j:G.ColorIndex):= LoopM i (Phone G j) false (Pawn.mold f 2) (Pawn.mold g 0) (fj j); intro W S;
         have ht(j:G.ColorIndex): (a j).B :=stampL _ _ _ (fun _ _=>tallJ _ _) _ _ (ScriptJ.key (tallJ _ _) (tallJ _ _)) (tallJ k _)
         have he(j:G.ColorIndex): draw (W*(a j ∘ t!)) L μ=0:=by
              let hz:=mintΓ hp hr (Phone G j) L x q f g μ c h z (fj j) (tallJ k _); with_reducible_and_instances exact hz
         rw [show (S ∘ (t!))=∑ j:G.ColorIndex,a j ∘ t! from funext fun x=>by change (∑ j,a j) _= _; rw[Finset.sum_apply,Finset.sum_apply];rfl, mul_sum,sumPry L μ _ _ ?_]; exact sum_eq_zero fun j _=> he j; exact fun j _=>height (WeightB hp x f g z) (turnB _ _ _ (ht j))
end
end YM.OPE.Merchant
