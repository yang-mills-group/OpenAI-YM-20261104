import YM.AllOrder.Floe.Runner
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
open PertExtension
namespace Pace
abbrev Scene (G:Gauge):= ℕ→Ink.Money.Bills (Coarse G)
def factor (q: Coin) (F:Scene G)(k:ℕ) (n:Side):= alters (fun i x=>q i) (fun i=>F i n) k
lemma weighs (q:Coin) (F:Scene G) (k:ℕ)(n:Side): factor q F k n=∑ i∈range (k+1),q i • F (k-i) n:= by unfold factor; rw [Fire.aligned]; rfl
lemma weigh_right (q:Coin)(F:Scene G)(k:ℕ)(n:Side): factor q F k n=∑ i∈range (k+1),q (k-i) • F i n:= by unfold factor; rw [commute,Fire.aligned]; apply Finset.sum_congr rfl; intro i hi; ext1; exact mul_comm ..
variable {F F' : Scene G}
def Valid (X:Scene G)(N:ℕ):Prop:=∀ j≤N,∀ n, Rank (rule (Coarse G) n) (j+2) (X j n) ∧ Etiquette X n j
namespace Valid
variable (h: Valid F N) (hk:k≤ N)
include h
lemma rank :∀ k≤N,∀ n, Rank (rule (Coarse G) n) (k+2) (F k n):=fun i k l=> (h i k l).1
lemma sub (H:Valid F' N):Valid (F-F') N:= fun j hj n => ⟨(h.rank j hj n).sub (H.rank j hj n), (h j hj n|>.2).less ((H j hj n).2) (fun i hi=>(h.rank i (hi.trans hj) _).read) (fun i hi=>(H.rank i (hi.trans hj) _).read) ⟩
lemma plusV (H:Valid F' N):Valid (F+F') N:=fun j hj n=>⟨(h.rank _ hj n).add (H.rank _ hj n),(h j hj n|>.2).adding (H j hj n|>.2) (fun i hi=>(h.rank i (hi.trans hj) _).read) (fun i hi=>(H.rank i (hi.trans hj) _).read) ⟩
lemma proceed (q:Coin):Valid (factor q F) N:=by
 let u(n:Side):Book (rule (Coarse G) n):= fun k x=> q k; let f n:Book (rule (Coarse G) n):=fun k=>F k n; intro j hj n; constructor; · rw [weighs]; exact Rank.sum (fun i _=> ((h.rank (j-i) (by omega) n).scal _).up (by omega))
 let X:= rule (Coarse G) n; have hk (v:ℝ→X): weigh v (u n)=q:= by
     let x:ℝ→X:=fun _=>0; funext i; exact congr_fun (weigh_const (q:=(0:X)) (u n)) i
 have hx (v:ℝ→X) (hv:ContDiffAt ℝ ω v 0): weigh v (fun i=>factor q F i n) j = Laplace.SigmaP.plus q (weigh v (f n)) j:= by
     change weigh v (alters (u n) (f n)) _=_; rw [weigh_mul hv (show Response.Budget _ (u n) N from (fun i _=>contDiffAt_const)) (fun i hi=> (h.rank _ hi n).read.smooth.contDiffAt) hj, hk]
 have he (v w:ℝ→X)(hv:ContDiffAt ℝ ω v 0)(hw:ContDiffAt ℝ ω w 0)(hu:∀ i≤N, weigh v (f n) i=weigh w (f n) i) : weigh v (fun i=>factor q F i n) j=weigh w (fun i=>factor q F i n) j:= by rw [hx v hv,hx w hw,plus_sum,plus_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [hu _ (by have hh:= mem_antidiagonal.mp hi; omega)]
 refine ⟨fun v w p x hv hw hp ht=>he v w hv hw (fun i hi=> (h i hi n|>.2.stain v w p x hv hw hp ht)),fun v s hv=> he v _ hv ((orderTurn s).contDiff.contDiffAt.comp _ hv) (fun i hi=> (h i hi n).2.sign v s hv)⟩
omit h
lemma void : Valid (G:=G) (0:Scene G) N:= fun k _ n=>⟨Rank.nil _ 0,⟨fun _ _ _ _ _ _ _ _=>rfl,fun _ _ _=>rfl⟩⟩
lemma sum {ι:Type*}{X:ι→Scene G}(s:Finset ι)(h:∀ i∈s,Valid (X i) N): Valid (∑ i∈s,X i) N:= by induction s using Finset.induction_on with
 | empty=> rw [sum_empty]; exact void
 | insert i s he ih=> rw [sum_insert he]; exact (h i (mem_insert_self ..)).plusV (ih fun i hi=> h i (mem_insert_of_mem hi))
end Valid
variable (q:Coin) (i:Age)(P: Layout G) (T:Finset Age)(p:Clip)(R:PathData G)
def base (p:Clip)(R:PathData G) : Scene G:= Haiku.Coat.clerk (fun _=>mainTerm p R) 2
def shiftB : Scene G:= base p R + Haiku.Coat.clerk (fun _=>Precision.loop R) 0 + factor q (base p R)
def moiety : Scene G:= factor (ladder (elapsed i) q) (Haiku.Coat.trade i.e (P i))
def glory : Scene G:=∑ i∈T, moiety q i P
def grouping : Scene G:=shiftB q p R +glory q P T
variable (h:R.Bounds p σ C Θ)
local notation "F[" n "]" => Stationary.Link G n
lemma valid_clerk {u:(n:Side)→ Config G n→ℝ}(h:Auditor u k)(hk:k≤2): Valid (clerk u k) N:= fun i _ n=>⟨((Project.maturity (X:=Stationary.Link G n) _ (i+k))).up (by omega),etiquette_clerk u h n i⟩ -- implicit binder
open Work.F05
include h
lemma intent_point (n:Side): Stationary.Pointwise (intended p R (m:=n)) := by rw [intent]; exact Stationary.Pointwise.add ((stain_knit R p h).add (stain_ink _ h.width h.three fun i=>(h.invariant i).2.1)) (stain_ink _ h.width h.four fun i=>(h.invariant i).2.2)
lemma audited (g:G.Simple): Auditor (fun n=>mainTerm p R (n:=n)) 2 := by
 intro n; let ht:= intent_point _ _ h n; refine ⟨?_, ht.analytic.contDiffAt, fun U V=> mainTerm_gauge h .., fun U s=> AnalyticNext.QuarticMatch.Joint.main_pull p R s 0 U⟩
 intro i hi h; funext r; rw [jet,show i=1 by omega]; change (↑(Nat.factorial 1):ℝ)⁻¹*iteratedFDeriv ℝ 1 (intended p R (m:=n)) 0 _=0; rw [Project.still_one g ht.stained ht.analytic]; simp
lemma base_pose (g:G.Simple): Valid (base p R) N := valid_clerk (audited p R h g) le_rfl
include h in
lemma loop_pose: Valid (clerk (fun _=> Precision.loop R) 0) N:= valid_clerk (fun n=> ⟨fun i hi=> by omega,(stain_ink _ h.width h.two fun i=>(h.invariant i).1).analytic.contDiffAt,fun u v=> loop_gauge h ..,fun u s=> orbit_axis (uncut _) u s⟩) (by omega)
omit h in
lemma moiety_pose (N:ℕ)(h:Legal T P)(ht:i∈T): Valid (moiety q i P) N:= by
 obtain ⟨a,B,hb,hx⟩:=h.rent i ht; apply Valid.proceed; exact fun k _ n=> ⟨trade_r i.e k n i.pricey,trade_et i.e hx hb (h.symm i ht) _ _⟩
lemma glories (hx:Legal T P)(g:G.Simple): Valid (grouping q P T p R) N := ((base_pose p R h g |>.plusV (loop_pose p R h)).plusV ((base_pose p R h g).proceed q)).plusV (Valid.sum T (fun i hi=> moiety_pose q i P T N hx hi))
end Pace
end YM.AllOrder.Floe
