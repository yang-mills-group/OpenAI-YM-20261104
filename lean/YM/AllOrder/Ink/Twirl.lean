import YM.AllOrder.Ink.Twine
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
variable (F:Stalk α α)
local notation "L"=> Slip (Point α)
local notation "X"=>rule α n
-- derivative cross dial. notation
abbrev there (z:Site n)(p:Point α) := stood z p
lemma coin (u v:L)(z y:Site n): spark F (invoice z u) (invoice y v)= ∑ i:LeafIdx u,∑ j:LeafIdx v, direct F n (stood z (knot u i)) (stood y (knot v j)) • (invoice z (eraseT u i) * invoice y (eraseT v j)):=by
 unfold spark; simp_rw [dab,inked,Finset.sum_mul,Finset.mul_sum,Finset.smul_sum]
 let H (i : Leaf n α)(j:Leaf n α)(p q):= direct F n i j • ((if stood z (knot u p)=i then invoice z (eraseT u p) else 0)*(if stood y (knot v q)=j then invoice y (eraseT v q) else 0));
 change (∑ i:Leaf n α,∑ j:Leaf n α,∑ p:LeafIdx u,∑ q:LeafIdx v,H i j p q)= _
 rw [show (∑ i:Leaf n α,∑ j:Leaf n α,∑ p:LeafIdx u,∑ q:LeafIdx v,H i j p q)=(∑ p:LeafIdx u,∑ q:LeafIdx v,∑ i:Leaf n α,∑ j:Leaf n α,H i j p q) from ?_]; swap
 · conv => lhs; arg 2; ext i; rw [sum_comm]; arg 2; ext p; rw [sum_comm]
   rw [sum_comm]; exact Finset.sum_congr rfl fun p _=> Finset.sum_comm
 unfold H; simp_rw [ite_mul,zero_mul,mul_ite,mul_zero,smul_ite,smul_zero]; -- ∑i∑j if i then if j. collapse
 apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _; simp
variable {x y: Slip (Point α)} {i:LeafIdx x}{j:LeafIdx y} (z:Site n) (w:Cover)
omit [Fintype α] in
lemma mirrored {u v:Point α} (y z:Site n): (stood y v).1=(stood z u).1+wrap n w ↔ z+wrap n (u.1+w-v.1)=y:= by simp only [stood, map_add, map_sub]; rw [← add_sub_assoc,sub_eq_iff_eq_add,add_assoc z,eq_comm]
-- fix
abbrev spur (F:Stalk α α)(v w:Slip (Point α))(p:LeafIdx v)(q:LeafIdx w)(i:Cover):= F (knot v p).2 (knot w q).2 i
omit [Fintype α] in
lemma latency (u v:L)(p:LeafIdx u)(q:LeafIdx v)(l:X)(h:Belt F a C)(ha:0≤a): HasSum (fun i: Cover=> spur F u v p q i * invoice z (jointI u v p q i) l) (∑ y:Site n,direct F n (stood z (knot u p)) (stood y (knot v q)) * (invoice z (eraseT u p) l * invoice y (eraseT v q) l)):= by
  let B (y:Site n):= invoice z (eraseT u p) l*invoice y (eraseT v q) l
  have hv (y:Site n):= (regional h ha (stood z (knot u p)) (stood y (knot v q))).mul_right (B y)
  apply (hasSum_sum (s:=Finset.univ) (fun i _=> hv i)).congr_fun; intro i
  simp_rw [mirrored,ite_mul,zero_mul]; rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ,if_true]; unfold B jointI; rw [invoice_add, lifted, Pi.mul_apply]; rfl
end Method
end YM.AllOrder.Ink
