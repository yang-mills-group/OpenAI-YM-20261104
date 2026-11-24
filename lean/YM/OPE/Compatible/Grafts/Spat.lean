import YM.OPE.Compatible.Grafts.View
/-!
# Ordinary and quotient paths. Poles
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)
local notation "X!"=> forest S.ratio he
local notation "Z!" => AxisChart G X!
local notation "K!" => Bid.Dir G c
local notation "U!" => Bid.Dir G f
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable {P:ChartRatio G}(ht:LocalRatio P)
open Flume.Script Shell Char Pilot Essay Arc
open Asymptotics
open Planned.PrimaryIntegral295.Carrier
section
variable {Q:Patch}{K':KernelChoices}(D:Boxes G Q K'){m:ℕ}
include ht
lemma scours (hs:G.Simple)(d:ℕ)(k:ℕ)(Y:Muse G)(f:ℝ)(hm:45≤k)(hH:Pathic d Y)(hx:Tide Y d k f)(hc:Era D A)(b:ℝ): Pathic d (rushS Q K' A b D P Y d)∧ ∃ f:ℝ,Tide (rushS Q K' A b D P Y d) d k f :=by
       let p:= rushS Q K' A b D P Y d; obtain ⟨N,hN⟩:= hc.bind; obtain ⟨s,z,he,hz,hQ⟩:= spineP Q K' D; obtain ⟨C,hc,H⟩:= costsS 1 k Q hs hm s z he hz K T P ht K' i d; let Φ: Telet Q D s z:=⟨hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2⟩; obtain ⟨w,hw,hp⟩:= gaV Q K' A P b k
       constructor
       · intro n x; let m(j:ℕ): Side:=⟨n.val*(j+N+1),mul_pos n.pos (by omega)⟩; have hm(j):n.val ∣ (m j).val:=⟨j+N+1,rfl⟩; have hd(j): j+N+1 ≤ (m j).val:=Nat.le_mul_of_pos_left _ n.pos
         choose L g hG using fun i:ℕ=>hN (m i) ((show N ≤ i +N+1 by omega).trans (hd i)); let S(i:ℕ):=subStud Q K' (m i); let t(i:ℕ):(S i).Choices:=Classical.arbitrary _; let X(i:ℕ):= Classical.choice (enrol (S i) _ D (t i) (hG i) b hs)
         let P'(j:ℕ):=wrap (m j) (lift x); let u(i):ScriptJ (Bid.Dir G (m i)):= TracePay (S i) _ D A (t i) (g i) P d Y b (P' i) (X i); have hv(i:ℕ):(tor (m i)).Marbles (u i):= hikeQ (S i) _ D (t i) (hG i) (X i) (hH _ _) hs ht
         have hh(j:ℕ):= H (m j) _ Φ _ _ A (L j) (g j) (hG j) (t j) (X j) (P' j) Y f hx w hw hp
         let W(j):=Booklet (hm j) G; let y(i:ℕ): ScriptJ (Bid.Dir G n):=u i ∘ W i
         have ht(x:ℕ): (tor n).Marbles (y x):=by
              refine ⟨fun i=> ((hv x).toll i).compLinear (W x).toLinearMap,fun {a b u} h=>?_⟩; apply ((hv x).honors (brink (hm x) h)).congr' _ Filter.EventuallyEq.rfl; filter_upwards with i; unfold y; simp only [Function.comp_apply]; erw [map_smul,map_smul]
         have hK:0 ≤ f:= Sack.coins ((hx 0).2 0); apply marFort y m (tendsto_atTop_mono (fun j=> (Nat.le_add_right j N|>.trans (Nat.le_succ _)) |>.trans (hd j)) tendsto_id) (inkM p d x) (glideZ d) (C*w^5*f) (by positivity) ht (meridian _ _ _ _ _ (hh 0).1); intro i j v; let q':= W i v; have hb := (hh i).2 q' j; apply le_trans _ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ 1+‖spool G (m i) q'‖ by positivity) (add_le_add_right (book_eq (hm i) v) 1) (glideZ d)) (show 0≤ C*w^5*f by positivity)) -- b:_
         change Mold ((u i (W i v)).seq j.val) ((inkM p d x v).seq j.val) _ _ _; rw [←show inkM p d (P' i) q'= inkM p d x v from (labRel (hm i) (P' i) v d p).trans (by rw [show trimT _ _ _ (P' i)= x from (lease (hm i) _).trans (wrap_lift x)])]; exact hb
       let n:Side:= ⟨N+1, Nat.succ_pos _⟩; obtain ⟨L,g,hg⟩:= hN n (Nat.le_succ _); let t:(subStud Q K' n).Choices:=Classical.arbitrary _; obtain ⟨X⟩:=enrol _ _ D t hg b hs; exact ⟨_,(H n D Φ _ _ A L g hg t X 0 Y f hx w hw hp).1⟩
end
variable {d':ℕ}{u':ℝ}{D':Alps K T d' u'}
include D'
lemma sprig (P:Flight i d')(X: Medal P.patch G K.K i)(h:Mag i d')(hp:A.gear=P.wing)(hh:D'.gear=P.land): Era (K':=K.K) (⟨i,h.1,X,A.gear⟩:Boxes G P.patch K.K) A:=by
       refine ⟨100* Pressure.macroR P.patch+2,fun n hn=>?_⟩; let S:=P.visit (f:=n*P.L) (c:=n) K.K rfl; have hs: Bid.Larger (G:=G) S:=by
            refine ⟨K.affordable _,?_,?_⟩; change _≤ n.val *P.L.val; apply (le_trans _ (Nat.le_mul_of_pos_right n.val P.L.pos)); exact (Nat.le_add_right _ _).trans hn
            omega -- transparency
       obtain ⟨g,hg⟩:= testimony _ _ _ A D' hp hh h X rfl hs
       exact ⟨_,g,hg.1⟩
end YM.OPE.Cascade.Rill
