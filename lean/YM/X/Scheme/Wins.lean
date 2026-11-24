import YM.X.Scheme.Nested
import YM.X.Journey.Bare
/-!
# Stable recalibration modulo near-Jet precritical real H frame (association joins).
Any-order statement, used in FO with singular shape estimates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Lattice Function Filter Set Pert Pert.Position Pulse Detector Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G}{d n:ℕ}
local notation "V"=> Buffer F d
local notation "B"=> Bank F d
namespace Ribbon
variable (a b c:Buffer F d)(D:Detector F d)
def followB (a b:Buffer F d):Buffer F d:= by
   let f:=(bufferL F a) ∘ₗ (bufferL F b); refine ⟨a.val*b.val,?_⟩
   refine ⟨?_,fun k hk p hp=> a.property.2.1 k hk (b.val p) (b.property.2.1 k hk p hp),fun p=>?_,fun s p=>?_,?_⟩
   · change a.val (b.val _)=0; rw [b.property.1,map_zero]
   · exact (a.property.2.2.1 _).trans (congr_arg a.val (b.property.2.2.1 _))
   · exact (a.property.2.2.2.1 s _).trans (congr_arg a.val (b.property.2.2.2.1 s _))
   exact map_smul f _
lemma follow_val : (followB a b).val = a.val*b.val:=rfl
lemma follows_right : Function.Injective (bufferL F (e:=d)):= by intro p q hp; exact Subtype.ext (ContinuousLinearMap.ext (fun i=> show p.val i=q.val i from LinearMap.congr_fun hp i))
lemma follow_buff : bufferL F (followB a b)= bufferL F a ∘ₗ bufferL F b:= LinearMap.ext fun _=> rfl
lemma plus_v (p q v:Buffer F d) (a:ℝ):followB (p+q) v=followB p v+followB q v ∧ followB (a • q) v=a • followB q v ∧ followB v (p+q)=followB v p+followB v q ∧ followB v (a • q)= a • followB v q:= by
    have he(x y:Buffer F d): (followB x y).val=x.val*y.val:= follow_val ..; refine ⟨?_,?_,?_,?_⟩ <;> (apply Subtype.ext; simp only [SetLike.coe_sort_coe,Submodule.coe_add, Submodule.coe_smul_of_tower,he]) -- edit
    all_goals (apply ContinuousLinearMap.ext;intro p; simp)
def passB : V→ₗ[ℝ] V→ₗ[ℝ] V := LinearMap.mk₂ ℝ followB (fun x y z=> (plus_v x y z 0).1) (fun a x y=> (plus_v x x y a).2.1) (fun x y z=>(plus_v y z x 0).2.2.1) (fun a x y=> (plus_v y y x a).2.2.2)
def settled : V×V → V:= fun p=> p.1+p.2+followB p.1 p.2
private lemma bills_smooth {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X](L':X→ₗ[ℝ] X→ₗ[ℝ] X): ContDiff ℝ ω (fun v:X×X=> L' v.1 v.2):= by
    let L:X→L[ℝ] X→L[ℝ] X:= L'.toContinuousBilinearMap; exact (L.contDiff.comp (f:= (Prod.fst:X×X→X)) contDiff_fst).clm_apply contDiff_snd
lemma settled_diff : ContDiff ℝ ω (settled (F:=F) (d:=d)):= by
    exact ContDiff.add (contDiff_fst.add contDiff_snd) (show ContDiff ℝ ω (fun v:Buffer F d × Buffer F d=> followB v.1 v.2) from (by exact bills_smooth (X:=Buffer F d) (passB (F:=F) (d:=d))))
lemma frame_settled : frameC F (settled (a,b))= frameC F a ∘ₗ frameC F b:= by apply LinearMap.ext;intro x; change x+(a.val x+b.val x+a.val (b.val x))= (x+b.val x)+a.val (x+b.val x); rw [map_add]; abel
lemma transferB (x:B): market F b (market F a x)=market F (settled (a,b)) x:= by unfold market;rw [pulls_join,frame_settled]
variable (p q:Word (Buffer F d))(x: Word (Bank F d))
def luxury := Jet.run (settled (F:=F)) (Jet.pair p q)
lemma together : predMarket q (predMarket p x) = predMarket (luxury p q) x:= by
   funext k; let X:= delay x k; let α:=delay p k; let β:=delay q k; have hX:= appears_delay x k; have ha:= Act.swell p (le_refl k); have hb:=Act.swell q (le_refl k); have hf:=appears_market (appears_market hX ha) hb; have hg:= appears_market hX ((ha.zipper hb).transit (m:=settled) settled_diff.contDiffAt); simp_rw [transferB] at hf; exact hf.same hg le_rfl
lemma voters : luxury p q 0 = settled (p 0,q 0):= run_zero ..
lemma coincideH (h:p 0=0)(hp:D.patch (x 0)): predMarket (D.report x) x=predMarket (D.report (predMarket p x)) (predMarket p x):= by
    let y:=predMarket p x; let w:=D.report y; have he0:y 0=x 0:= by unfold y;rw [pred_zero,h,market_zero];
    have hz:= D.patch_announces (w:=y) (by rw [he0]; exact hp); rw [together]; apply congr_arg (predMarket · x) (Eq.symm (D.patch_only hp ?_ ?_)); rw [voters,h]; change settled (0,w 0)= _; unfold w; rw [report_zero,he0]; apply Subtype.ext; simp [settled,follow_val]
    unfold announce;rw [← together]; exact hz
end Ribbon
end YM.PositionX
