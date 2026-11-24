import YM.AllOrder.Floe.Faith
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
-- Param induction at age.grade (offset k). benchmark √ warp Stage rank. quote.`(e+2)` Rank.R<=. Restore extra pieces all ranks now. hZ unit absorb.We.Pro.Cut.
abbrev rank (k:ℕ) := k+3
local notation "r"=> Step.rank k
local notation "v"=> Age.scope
abbrev entry (k:ℕ)(i:Fin (k+4)):Age:=⟨k,i,(by have he:= i.isLt; omega)⟩
abbrev upto (k:ℕ):Finset Age:= Finset.univ.image fun i=> entry k i
def bottom (k:ℕ):Age:= entry k 0
lemma liesH (i:Age)(he:i.grade=k):∀ h,entry k (⟨i.slots,h⟩)=i:=by rintro h; rcases i with ⟨t,i,hx⟩; obtain rfl : t=k:= he; rfl
lemma tier (i:Age): i∈upto k↔ i.grade=k:= ⟨fun he=> by obtain ⟨j,-,rfl⟩:=Finset.mem_image.mp he;rfl, fun he=> by have hx:i.slots<k+4:= (by have hv:=i.paid;omega); exact Finset.mem_image.mpr ⟨⟨_,hx⟩, Finset.mem_univ _, liesH i he hx⟩⟩
lemma born_height (i:Age)(h:i∈upto k): i.e= Step.rank k:= by unfold Age.e; rw [(tier i).1 h]
lemma earlier (i:Age)(h:i∈tape (k+2)): i.e < r:= by have he:=Age.in_scope.mp h; unfold Step.rank; omega
lemma revealed (k:ℕ): upto k∪ tape (k+2)= tape (rank k):= by ext i; rw [Finset.mem_union,tier]; simp only [tier,Age.in_scope,tape,Age.e,rank]; omega
lemma fresh_set (k:ℕ): Disjoint (upto k) (tape (k+2)):= Finset.disjoint_left.mpr (fun i hi hj=> by have h:= born_height i hi; have ht:= earlier i hj; omega)
variable (k) {Q Q':Coin} (p:Clip) (R : PathData G)(U U':Layout G)
section amendments
variable (hx:∀ i∈tape (k+2), U' i=U i) (hQ: ∀ i < Step.rank k,Q i=Q' i)
local notation "X"=> tape (k+2)
local notation "Z"=> tape (rank k)
include hx hQ
lemma shades {n:ℕ}(hn:n<r): grouping Q U X p R n= grouping Q' U' Z p R n:= by
 rw [glints X (fun i hi=>(hx i hi).symm) (fun i (hi:i≤n)=> hQ i (hi.trans_lt hn)) n le_rfl, ← revealed k]; unfold grouping glory; rw [sum_union (fresh_set k)]; change _+_= _ + ((∑ i∈upto k,moiety Q' i U')+(∑ i∈X,moiety Q' i U')) n -- holes
 rw [Pi.add_apply]; rw [Finset.sum_apply (s:=upto k),Finset.sum_eq_zero (fun i (hi:i∈upto k)=>moiety_thin (P:=U') i (q:=Q') (hn.trans_eq (born_height i hi).symm)),zero_add]
omit hQ
variable (hQ0:light Q')
include hQ hQ0
lemma painted (j:Side)(H: Scene G): ask p R H Q' Z U' r j=ask p R H Q X U r j-(Q' r-Q r) • (Pace.base p R 0 j)-∑ i∈ upto k, jet (turnSeries (m:=j) (U' i)) i.r:= by
 have he:glory Q' U' Z r j=glory Q' U' X r j+ ∑ i∈ upto k, jet (turnSeries (m:=j) (U' i)) i.r:=by
    rw [← revealed]; unfold glory; rw [sum_union (fresh_set k),Pi.add_apply,Pi.add_apply,add_comm]; apply congr_arg; rw [Finset.sum_apply,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i hi; rw [← born_height i hi]; exact moiety_now hQ0 i j
 have hv:= tip_corr X hx (q:=Q') (d:=Q) (fun i hi=>(hQ i hi).symm) (j:=r) (R:=R) (p:=p) (by unfold Step.rank; omega) j
 let f:= ∑ i∈ upto k, jet (turnSeries (m:=j) (U' i)) i.r; have hz:grouping Q' U' Z p R r j= grouping Q' U' X p R r j + f:= by unfold grouping; simp only [Pi.add_apply]; rw [he,← add_assoc];
 change 0 - H r j -grouping Q' U' Z p R r j=(0-H r j-grouping Q U X p R r j)-_ -_; rw [hz, (eq_add_of_sub_eq hv)]
 abel -- using hv via eq.solve
end amendments
end YM.AllOrder.Floe.Step
