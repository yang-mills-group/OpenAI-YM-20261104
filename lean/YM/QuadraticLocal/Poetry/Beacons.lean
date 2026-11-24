import YM.QuadraticLocal.Poetry.Pickets
/-!
# Table vs site in every charge when registered at an actual marker root
 ASSIGN independent spurion lights everywhere and cut out all copies outside.Z.C.
:/
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money GaussianScore Module Push
open Sunrise Sunrise.Focus
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n m:Side}{a C D b:ℝ}{k:ℕ}
variable {V α M:Type}[Fintype α][Fintype M][DecidableEq M] (T:Finset M)(q:M)
local notation "J"=> α⊕M
local notation "Ω"=> Point (α⊕M)
local notation "U"=>rule J n
-- Receipt.Memory at μ.Z,
namespace Picket
variable (hq:q∈T) (F:AllOrder.Ink.Field (α⊕M))(hp:Fixed T q F) (u:rule α n)(v:rule M n)
local notation "q'"=> ((0, Sum.inr q):Point (J))
def pinpoint (x:Site n) (z:rule M n): rule M n := fun i=> if i.2=q ∧ i.1≠x then 0 else z i
-- uniqueness of marker first (inside coordinate, root all y(v)).
lemma separate {L:Slip (Point (α⊕M))}{r s:Cover} (h:tally L q ≤1) (h':(r,Sum.inr q) ∈ L)(hz:(s,Sum.inr q)∈L):r=s:= by
 induction L with
 | nil=> simp at h'
 | cons i L ih=>
    rw [stamped] at h; have hh:tally L q ≤ 1:= (Nat.le_add_left ..).trans h
    rcases List.mem_cons.mp h' with H|H <;> rcases List.mem_cons.mp hz with H'|H'; exact congr_arg Prod.fst (H.trans H'.symm)
    · rw [←H] at h; simp only [calls,Sum.elim_inr,if_true] at h; have hx:= (counts q L).mpr ⟨_,H'⟩; omega
    · rw [←H'] at h; simp only [calls,Sum.elim_inr,if_true] at h; have hx:= (counts q L).mpr ⟨_,H⟩; omega
    exact ih hh H H'
variable (x:Site n)
lemma sole (w:Ω) {L:Slip (Point (α⊕M))}(hw:w∈ L)(h:tally L q≤1)(hp:q'∈ L) : mingle u (pinpoint q x v) (stood x w)=mingle u v (stood x w):= by
 obtain ⟨i,z|z⟩:=w; · rfl
 change (if z=q∧ _ ≠_ then _ else _) = _; refine if_neg (fun he=> ?_); obtain ⟨rfl,hz⟩:=he; rw [separate _ h hw hp] at hz; apply hz; simp [stood] -- may binder q subst z
lemma soloI (L: Slip (Point (α⊕M)))(h:tally L q≤1)(hp:q'∈ L) : invoice x L (mingle u (pinpoint q x v)) = invoice x L (mingle u v):= by
 unfold invoice paid; rw [List.map_map,List.map_map]; refine congr_arg List.prod (List.map_congr_left (fun i hi=> sole q u v x i hi h hp))
lemma voidI (L:Slip (Point (α⊕M)))(hp:q'∈ L)(y:Site n)(hy:y≠x): invoice y L (mingle u (pinpoint q x v))=0:=by
 unfold invoice paid; apply List.prod_eq_zero -- maybe ↔
 apply List.mem_map.mpr; refine ⟨stood y ((0,Sum.inr q):Point J), List.mem_map_of_mem hp, ?_⟩; change pinpoint q x v (y+wrap n 0,q)=0; unfold pinpoint; rw [if_pos (by simp [hy])]
include hp
lemma Fixed.receipt : F.table n (mingle u (pinpoint q x v))=F.site n x (mingle u v):= by
 rw [Field.table_apply,Finset.sum_eq_single x]; · unfold Field.site; refine tsum_congr fun i=>?_ ; have hm:tally _ q ≤ 1:= le_trans ((hp.tracked i q).le) (by split <;> omega); rw [soloI q u v x (F.slip i) hm (hp.root i)]
 intro y _ hy; unfold Field.site; simp_rw [show ∀ i,invoice y (F.slip i) (mingle u (pinpoint q x v))=_ from fun i=> voidI q u v x (F.slip i) (hp.root i) y hy]; simp
 simp
end Picket
end YM.QuadraticLocal.Poetry
