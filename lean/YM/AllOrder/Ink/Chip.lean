import YM.AllOrder.Ink.Lap
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Method
open Field GaussianScore
variable (F:Stalk α α) (X:Field α)
local notation "P"=> Point α
local notation "U"=> Slip (Point α)
variable {x:Slip (Point α)}
def Held (S: Slip (Point α)) := (i: LeafIdx S) × LeafIdx (eraseT S i)
instance (S: Slip (Point α)): Fintype (Held S):= inferInstanceAs (Fintype (Sigma _)) -- fix
abbrev senior (S:U)(i:Held S): Point α:= knot S i.1
abbrev secondary (S:U)(i:Held S): Point α:= knot (eraseT S i.1) i.2
abbrev child (S:U)(i:Held S):= eraseT (eraseT S i.1) i.2
abbrev funds (x:U)(i:Held x):= F (senior x i).2 (secondary x i).2 (reach (senior x i) (secondary x i))
abbrev trim (n:Side) (x:U)(i:Held x):= gap F (0:Site n) (senior x i) (secondary x i)
abbrev functionary (u v:Point α):= reach u v
omit [Fintype α] in
lemma rust (x:U)(i:Held x): meter (child x i)+size (functionary (senior x i) (secondary x i)) ≤ meter x := by
  calc _ ≤ _ + (size (secondary x i).1 +size (senior x i).1):= by
             apply Nat.add_le_add_left; unfold functionary reach; rw [sub_eq_add_neg]; exact (size_add _ _).trans_eq (congr_arg (size (secondary x i).1+·) (size_neg _))
       _ = _ := by unfold secondary senior child; rw [← add_assoc, ending (eraseT x i.1) i.2, ending x i.1]
omit [Fintype α] in
lemma ranks (h:x.length ≤ k) (i:Held x) : (child x i).length ≤ k-2:= by
 have he := List.length_eraseIdx_add_one (l:=x) i.1.isLt; have hx:= List.length_eraseIdx_add_one (l:=eraseT x i.1) i.2.isLt; change (child x i).length+1=(eraseT x i.1).length at hx; change (eraseT x i.1).length+1=x.length at he; omega
lemma flicker_seat (x:U)(z:Site n): flicker F n (invoice z x)=∑ i:Held x,(direct F n (stood z (senior x i)) (stood z (secondary x i))) • invoice z (child x i):= by
   unfold flicker; -- use D formula
   let u(p : LeafIdx x):=stood z (knot x p); let v(p : LeafIdx x)(q: LeafIdx (eraseT x p)):=stood z (knot (eraseT x p) q)
   let A:BoardL n α α:=direct F n; have hx(i j:Leaf n α)(p:LeafIdx x) : Plausible (if u p=i then invoice z (eraseT x p) else 0) := by split; exact (ticket ..).2.1.read; exact Plausible.atom 0
   let T₀ p q:=invoice z (eraseT (eraseT x p) q); have he(i:Leaf n α)(p:LeafIdx x) (j:Leaf n α):
       dab j (if u p=i then invoice z (eraseT x p) else 0)= if u p=i then ∑ q:LeafIdx (eraseT x p),if v p q=j then T₀ p q else 0 else 0:= by
       by_cases hh:u p=i <;> simp only [hh,if_pos,if_neg]
       · exact inked _ _ (eraseT x p)
       exact dift ..
   have H(i j:Leaf n α): dab j (dab i (invoice z x)) = ∑ p:LeafIdx x, if u p=i then ∑ q:LeafIdx (eraseT x p),if v p q=j then T₀ p q else 0 else 0:= by
      rw [show dab i _= ∑ p:LeafIdx x, if u p=i then invoice z (eraseT x p) else 0 from inked ..]; unfold dab; rw [tout _ (fun p _=>hx i j p)]; exact Finset.sum_congr rfl fun p _=> he i p j
   simp_rw [H, Finset.smul_sum]; change (∑ i:Leaf n α,∑ j:Leaf n α,∑ p:LeafIdx x,_)= ∑ y : (i: LeafIdx x) × LeafIdx (eraseT x i),_; rw [sum_comm,Fintype.sum_sigma]; -- now ∑ j ∑ i. nest outer via sum_comm & drawT
   change (∑ j:Leaf n α,∑ i:Leaf n α,∑ p:LeafIdx x,A i j• if u p=i then ∑ q:LeafIdx (eraseT x p),if v p q=j then T₀ p q else 0 else 0)=_; simp_rw [show ∀ j : Leaf n α,(∑ i:Leaf n α,∑ p:LeafIdx x,A i j • if u p=i then ∑ q:LeafIdx (eraseT x p),if v p q=j then T₀ p q else 0 else 0)=∑ p:LeafIdx x,∑ i:Leaf n α,A i j• if u p=i then ∑ q:LeafIdx (eraseT x p),if v p q=j then T₀ p q else 0 else 0 from fun j=>sum_comm]
   rw [sum_comm]; refine Finset.sum_congr rfl fun p _=>?_ ; simp_rw [smul_ite,smul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true, Finset.smul_sum, smul_ite,smul_zero] -- now by j
   rw [sum_comm]; simp_rw [Finset.sum_ite_eq,Finset.mem_univ,if_true]; rfl
end Method
end YM.AllOrder.Ink
