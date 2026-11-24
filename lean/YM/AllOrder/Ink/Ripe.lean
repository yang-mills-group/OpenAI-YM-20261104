import YM.AllOrder.Ink.Chip
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
variable (F:Stalk α α)(X:Field α)
local notation "P"=> Point α
local notation "U"=> Slip (Point α)
def plan (V:∀ x:Slip (Point α),Held x→ℝ): Field α where
 Ty:= (i:X.Ty) × Held (X.slip i)
 fee i:= X.fee i.1*V (X.slip i.1) i.2
 slip i:= child (X.slip i.1) i.2
-- testing BOTH in physical budget and cure.
omit [Fintype α] in
lemma cardinal (x:Slip (Point α))(h:x.length ≤ k) : Fintype.card (Held x) ≤ k*k:= by
 change Fintype.card ((i:LeafIdx x) × LeafIdx (eraseT x i))≤ _; rw [Fintype.card_sigma]; refine (Finset.sum_le_sum (g:=fun _=>k) (fun i _=> ?_)).trans ?_; · change Fintype.card (Fin (eraseT x i).length)≤ _; rw [Fintype.card_fin]; exact (by have hh:= List.length_eraseIdx_add_one (l:=x) (i.isLt); unfold eraseT; omega)
 change ∑ _ : Fin x.length, k≤ _; simpa using Nat.mul_le_mul_right k h
omit [Fintype α] in
lemma plan_v {V:∀ x : Slip (Point α),Held x→ℝ}(hD:0≤D)(H:X.Good a C k)(h:∀ x(z:Held x), Real.exp (a*meter (child x z))* |V x z|≤ Real.exp (a*meter x)*D) : (plan X V).Good a ((k*k:ℕ)*(D*C)) (k-2):= by
  refine ⟨fun i=> ranks (H.length i.1) i.2,sumBudget_sigma (a:=fun i=> (k*k:ℕ)*(D*X.price a i)) ?_ (budget_scale (Nat.cast_nonneg _) (budget_scale hD H.pay))⟩
  intro i; let S:= X.slip i; let Z:= plan X V; let u:= D*X.price a i; apply budget_finite (f:=fun j:Held S=>Z.price a ⟨i,j⟩) (fun j=> Z.price_nonneg _ _)
  refine (Finset.sum_le_sum (g:=fun _=>u) (fun j _=>?_)).trans ?_
  · unfold Field.price; change Real.exp (a*meter (child S j))* |X.fee i*V S j|≤ _; rw [abs_mul,mul_left_comm]; refine (mul_le_mul_of_nonneg_left (h S j) (abs_nonneg _)).trans_eq ?_; unfold u Field.price S; ring
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (cardinal _ (H.length i))) (mul_nonneg hD (X.price_nonneg ..))
variable (H:X.Good a C k) (h:Belt F a D)(ha:0≤a)(hD:0≤D)
omit [Fintype α]
include h H ha hD
lemma crux : (plan X (funds F)).Good a ((k*k:ℕ)*(D*C)) (k-2) := by
 apply plan_v X hD H; intro x z; let u:=senior x z; let v:=secondary x z;
 have ht: |funds F x z|≤D:= budget_single ((h u.2 v.2).unweighted ha) _
 refine (mul_le_mul ?_ ht (abs_nonneg _) (Real.exp_pos _).le); apply Real.exp_monotone; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((Nat.le_add_right _ _).trans (rust ..))) ha
lemma critical (n:Side): (plan X (trim F n)).Good a ((k*k:ℕ)*((Real.exp (-a*n.val)*D)*C)) (k-2) := by
 apply plan_v X (mul_nonneg (Real.exp_pos _).le hD) H; intro x z; let u:=senior x z; let v:=secondary x z; refine (mul_le_mul_of_nonneg_left (fare_gap (x:= (0:Site n)) h ha u v) (Real.exp_pos _).le).trans ?_; rw [← mul_assoc,← mul_assoc (Real.exp (a*↑(meter x))), ←Real.exp_add,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ hD; apply Real.exp_monotone; have ht:(meter (child x z):ℝ)+size (reach u v)≤ meter x:=by exact_mod_cast rust x z
 nlinarith
end Method
end YM.AllOrder.Ink
