import YM.AllOrder.Plateau.Slim
/-!
# Peak orientation, awareness by compressed view: Enter without resetting any W counts. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau.Slim
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open Song AbsoluteSums AbsoluteSums.Animals Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n m q: Side} {k j w N : ℕ}
variable {σ C Z β x₀:ℝ} (p:BudgetPoint)
local notation "E"=>Positions (Primary n G)
open Trio Slide Marlin
lemma matched (A: Track q) (x:Site m)(y:Site n)(U:Config G m)(V:Config G n) (w:ℕ) (h:∀ i,Slide.stage A i∈Lattice.box w) (H: Agrees (Lattice.box w) (expandAt x U) (expandAt y V)): Slide.shape A x U= Slide.shape A y V:= by
  funext ⟨i,l⟩; have he:= tops A i l; unfold Slide.shape; split; rename_i hi;
  · apply H (Slide.stage A i,l) (h i); change Slide.stage A i + _ ∈ Lattice.box w; rw [hi,one_smul] at he; exact he ▸ h _
  split; rename_i hD; rw [hD,neg_one_smul,← sub_eq_add_neg] at he; exact congr_arg Inv.inv (H (Slide.stage A (i+step l),l) (h _) (show Slide.stage A (i+step l)+step l∈ Lattice.box w from (by rw [he,sub_add_cancel]; exact h _))); rfl -- split;

variable {Y:Stars→Side}(Q:∀ i:Stars,(Y i).val=2*(w+i.val))(X:∀ i:Stars,Offer G (Y i))
include Q
lemma sense (hp:w+4≤k): gardenfold k (fun c:Side=>ornament Q (c:=c) X):= by
 intro n m i j U V h; unfold ornament beacon; refine Finset.sum_congr rfl fun k' _=>?_ ; have hp' : ∀ i, Slide.stage (pad Q k') i∈Lattice.box k:= by
    intro t; refine Finset.Icc_subset_Icc ?_ ?_ (crystal_le _ (Slide.stamp (Q k').ge t));
    · intro y; apply neg_le_neg; apply Int.ofNat_le.mpr; have ht:=k'.isLt; omega
    intro i; apply Int.ofNat_le.mpr; have ht:=k'.isLt; omega
 apply congr_arg; apply Finset.sum_congr rfl; intro l _; unfold unit; rw [matched (pad Q k') i j U V k hp' h]
variable (f:∀ c: Side,Offer G c) (h:gardenfold k f)
abbrev portion (x:Site n) (U:Config G n) (θ:Seat n) := f n ((turnS θ).symm x) (θ.view U)
include h
omit Q
lemma between (x:Site n)(y:Site m)(U:Config G n)(V:Config G m)(s:Signed)(a:Site n)(b:Site m)(he:Agrees (Lattice.box k) (expandAt x U) (expandAt y V)): portion f x U (s,a)= portion f y V (s,b):= by
 apply h; unfold Seat.view; simp only [expandAt_pull]; have ht {n} (b x: Site n): Lattice.affine s b ((turnS (s,b)).symm x)=x:=(turnS (s,b)).apply_symm_apply x
 simp_rw [ht]; exact agree_turn s 0 k _ _ he
lemma condensed (x:Site n)(U:Config G n): paid (f n) x U= Patch.average fun s=> portion f x U (s,0) := by
 unfold paid; rw [Finset.sum_apply]; have hh(s:Signed)(b:Site n): choir (f n) (θdoor (s,b) x) U= Song.Rim n* portion f x U (s,0):= by rw [← between f h x x U U s b 0 (fun _ _ _=>rfl)]; rfl
 rw [Fintype.sum_prod_type]; simp_rw [hh, sum_const,card_univ,nsmul_eq_mul]; unfold Patch.average Song.Rim Seat; simp only [Fintype.card_prod,Nat.cast_mul,_root_.mul_inv_rev]; have he:(Fintype.card (Site n):ℝ)≠ 0 := (by positivity); simp_rw [← mul_assoc, mul_inv_cancel₀ he,one_mul,Finset.mul_sum]
lemma paid_local : gardenfold k fun n => paid (f n):= by intro n m i j U V H; dsimp only; rw [condensed f h,condensed f h]; exact congr_arg _ (funext fun s=> between f h i j U V _ 0 0 H) -- arg id
omit h
lemma signed_sense {p:Offer G n} (hp:Mirrors p) (U:Config G n)(θ:Seat n): Trio.froth p (θ.view U)=Trio.froth p U:= by -- omit h
 unfold froth Seat.view; simp_rw [show ∀ v : Site n,p v (pull θ.1 θ.2 U)=_ from fun v=> hp ..]; exact Equiv.sum_comp (turnS θ) (fun i=> p i U)
end YM.AllOrder.Plateau.Slim
