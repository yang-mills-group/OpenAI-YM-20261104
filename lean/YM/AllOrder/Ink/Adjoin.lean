import YM.AllOrder.Ink.Flow
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
local notation "X"=> rule α n
abbrev spark (f g: X→ℝ):= ∑ i:Leaf n α,∑ j:Leaf n α,direct F n i j • (dab i f*dab j g)
lemma spark_zero (f:X→ℝ): spark F f 0=0 ∧ spark F 0 f=0:=by unfold spark; simp_rw [show ∀ i:Leaf n α, dab i 0=0 from fun i=> dift ..]; simp
lemma toolA (k:ℕ)(w:X→ℝ)(x:X): LinTest X k (fun f=> spark F w f x) ∧ LinTest X k (fun f=> spark F f w x):= by
 constructor <;> constructor <;> intro f g h
 · intro H; unfold spark dab; simp_rw [adds h.read H.read, mul_add,smul_add,Finset.sum_add_distrib]; rfl
 · unfold spark dab; simp_rw [scalars h.read, mul_smul_comm, smul_comm (direct F n _ _) g, ←Finset.smul_sum]; rfl
 · intro H; unfold spark dab; simp_rw [adds h.read H.read, add_mul,smul_add,Finset.sum_add_distrib]; rfl
 · unfold spark dab; simp_rw [scalars h.read,smul_mul_assoc, smul_comm (direct F n _ _) g, ←Finset.smul_sum]; rfl
lemma spark_est (k l:ℕ){u v:X→ℝ}{P D:ℝ}(h:Belt F a P)(hA:0≤a)(hu:Prices k C u)(hv:Prices l D v): Prices ((k-1)+(l-1)) (((Fintype.card (Leaf n α):ℝ)) * (((Fintype.card (Leaf n α):ℝ)) * (P*((C*honor k)*(D*honor l))))) (spark F u v) := by
  have hq(i:Leaf n α): ‖spot i‖≤1:= (norm_bolt i).le
  have ht:= price_sum (k:=(k-1)+(l-1)) («X»:=X) (univ:Finset (Leaf n α)) (f:=fun i=> ∑ j:Leaf n α,direct F n i j • (dab i u*dab j v)) (fun i _=> price_sum (k:=(k-1)+(l-1)) (C:=fun _=>P*((C*honor k)*(D*honor l))) (univ:Finset (Leaf n α)) (f:=fun j=>direct F n i j • (dab i u*dab j v)) (fun j _=>?_)); --  (univ:Finset (Leaf n α)) (fun i _=> price_sum (univ:Finset (Leaf n α)) (fun j _=>?_)); -- third goal type meta
  · unfold spark; simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using ht
  exact price_mono (price_scale (price_mul (hu.taper (spot i) (hq i)) (hv.taper (spot j) (hq j))) _) (mul_le_mul_of_nonneg_right (h.norm_direct hA i j) (mul_nonneg (mul_nonneg hu.1 (honor_pos _).le) (mul_nonneg hv.1 (honor_pos _).le)))

-- operate on leaves then tables
end Method
end YM.AllOrder.Ink
