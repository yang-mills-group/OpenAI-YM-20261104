import YM.AllOrder.Floe.Era
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
open Haiku.Coat
namespace Pace
variable {q d:Coin}{p:Clip}{P P':Layout G}{R:PathData G} (h0: light q)(T:Finset Age) (i:Age)
variable (ht:∀ j∈T,P j=P' j)
-- geometry relations not using price. Path PPE. No work in knot outside cone.
include ht
lemma adorn (F:Age→ Scene G) (F':Age→ Scene G) (he:∀ j∈T,F j=F' j) : (∑ i∈T,F i)=∑ i∈T,F' i:= Finset.sum_congr rfl he -- unused
omit ht
lemma moiety_thin (h:k < i.e) : moiety q i P k=0:= by
 funext n; unfold moiety; rw [weighs]; apply Finset.sum_eq_zero; intro p hp; rw [trade,if_neg (show ¬i.e ≤ k-p from by omega),smul_zero]
include h0
lemma moiety_now (n:Side): moiety q i P i.e n=jet (turnSeries (P i) (m:=n)) i.r:= by
 rw [moiety,weighs,sum_eq_single 0, start (elapsed i) h0,one_smul,trade,Nat.sub_zero,if_pos le_rfl, Nat.sub_self, Nat.zero_add]; intro j hj he; rw [trade,if_neg (by have hh:= mem_range.mp hj; omega),smul_zero]; simp
omit h0
local notation "f0"=> grouping q P T p R
local notation "f1" => grouping d P' T p R
include ht
lemma hold (he:fitto q d j) : ∀ n:ℕ, n≤j → glory q P T n=glory d P' T n := by
 intro k hk; funext n; simp_rw [glory,Finset.sum_apply]; refine Finset.sum_congr rfl (fun i hi=>?_); unfold moiety; rw [ht i hi,weighs,weighs]; exact Finset.sum_congr rfl (fun l hl=> by rw [synch he _ _ ((Nat.le_of_lt_succ (Finset.mem_range.mp hl)).trans hk)])
-- request predecessor strictly positive orders k−3 max≥? If k=1 strict(0). 
lemma hold_up (he:fitto q d (j-1)) : glory q P T j=glory d P' T j := by
 funext n; simp_rw [glory,Finset.sum_apply]; refine Finset.sum_congr rfl (fun i hi=>?_); unfold moiety; rw [ht i hi,weigh_right,weigh_right]; refine Finset.sum_congr rfl fun l hl=>?_; unfold trade; split; rename_i hk; rw [synch he _ _ (by have :=i.senior; omega)]; simp
lemma tip_corr (he:∀ i<j, q i=d i)(hk:1≤j)(n:Side): f0 j n-f1 j n=(q j-d j) • base p R 0 n:= by
 unfold grouping; simp only [Pi.add_apply]; rw [hold_up T ht (fun i hi=>he i (by omega)), add_sub_add_right_eq_sub]; unfold shiftB; simp only [Pi.add_apply]; rw [add_sub_add_left_eq_sub,weighs,weighs,← sum_sub_distrib,sum_eq_single j, Nat.sub_self,sub_smul]; intro i hi he'; rw [he _ (by have hh:=mem_range.mp hi; omega),sub_self]; simp
lemma glints (he:fitto q d k) : fitto f0 f1 k:= by
 intro j hj; funext n; unfold grouping; simp only [Pi.add_apply]; rw [hold T ht he _ hj]; unfold shiftB; simp_rw [Pi.add_apply]; rw [weighs,weighs]; exact congr_arg (fun v=>_+v+_) (sum_congr rfl fun l hl=> by rw [he l ((Nat.le_of_lt_succ (Finset.mem_range.mp hl)).trans hj)]) -- metavars
-- introducing new P(i) while leaving old as d← partitions
variable (hi:i∉T)
include hi
lemma bean (n:ℕ) : glory q P' (insert i T) n= moiety q i P' n+ glory q P T n:= by simp_rw [glory,sum_insert hi,Pi.add_apply]; exact congr_arg (moiety q i P' n+·) (hold T (fun j hj=>(ht j hj).symm) (q:=q) (fun j _=>rfl) _ (le_refl n))
lemma cork  (hk:k < i.e): grouping q P' (insert i T) p R k=f0 k:= by unfold grouping; rw [Pi.add_apply, bean T i ht hi _, moiety_thin i hk,zero_add]; rfl
include h0
lemma fore (n:Side): grouping q P' (insert i T) p R i.e n=f0 i.e n+ Radial.jet (turnSeries (P' i) (m:=n)) i.r:= by unfold grouping; rw [Pi.add_apply,Pi.add_apply, bean T i ht hi _,Pi.add_apply,moiety_now h0 i n]; simp only [Pi.add_apply]; abel
end Pace
end YM.AllOrder.Floe
