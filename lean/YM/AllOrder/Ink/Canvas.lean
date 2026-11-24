import YM.AllOrder.Ker.Seats
import YM.AllOrder.Fire.PriceR
import YM.Push.LOCAL_SPLITTING.Budget
import YM.Push.ABSOLUTE_SUMS.Basic
/-!
# Rooted post tape

An implementation of finitely polarized Laurent quantities. Don't identify
ambiguous masses via Fourier winding. Literals in `brush β k` pay EVERY
entry and support weight (formal). May realize leaf tags and baseRows. Period
error prices come later separately. Rank selection for normalization earns
from actual kernels. Fin and Sigma counts deliberate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
section algebra
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
open Classical
lemma Prices.up (h:k ≤ N){f:X→ℝ}(he:Prices k C f) : Prices N C f:= ⟨he.1,he.2.1.up h,fun i=>(he.2.2 i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) h) he.1)⟩
lemma price_add {f g:X→ℝ}(h:Prices k C f)(H:Prices k D g): Prices k (C+D) (f+g):= by
 refine ⟨add_nonneg h.1 H.1,h.2.1.add H.2.1,fun i=>?_⟩; rw [add_mul]; exact (abs_add_le _ _).trans (add_le_add (h.2.2 i) (H.2.2 i))
lemma price_scale {f:X→ℝ}(h:Prices k C f)(b : ℝ): Prices k (|b| *C) (b•f):= by
 refine ⟨mul_nonneg (abs_nonneg _) h.1,h.2.1.scal _,fun i=>?_⟩; rw [Pi.smul_apply,smul_eq_mul,abs_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.2.2 i) (abs_nonneg _)
lemma price_mul {f g:X→ℝ}(h:Prices N C f)(H:Prices k D g):Prices (N+k) (C*D) (f*g):= by
 refine ⟨mul_nonneg h.1 H.1,h.2.1.mul H.2.1,fun i=>?_⟩; rw [Pi.mul_apply,abs_mul,pow_add,mul_mul_mul_comm]; exact mul_le_mul (h.2.2 i) (H.2.2 i) (abs_nonneg _) (mul_nonneg h.1 (by positivity))
lemma price_mono {f:X→ℝ}(h:Prices k C f)(he:C ≤ D): Prices k D f:=⟨h.1.trans he,h.2.1,fun i=>(h.2.2 i).trans (mul_le_mul_of_nonneg_right he (by positivity))⟩
lemma price_const (h:|a|≤C)(k:ℕ):Prices k C (fun (_:X)=>a):= ⟨(abs_nonneg _).trans h,Rank.nil k a,fun i=> le_trans (le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg i)))) (mul_le_mul_of_nonneg_right h (by positivity))⟩
lemma price_sum {ι:Type*} (S: Finset ι) {f:ι→X→ℝ}{C:ι→ℝ}(h:∀ i∈S,Prices k (C i) (f i)): Prices k (∑i∈S,C i) (∑i∈S,f i):= by
 induction S using Finset.induction_on with | empty=> simp only [Finset.sum_empty]; exact price_const (X:=X) (le_of_eq (abs_zero ..)) k | insert i S hi ih=> rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact price_add (h i (mem_insert_self ..)) (ih (fun i hi=> h i (mem_insert_of_mem hi)))
end algebra

abbrev Point (α:Type):= Cover×α
abbrev Slip (ι:Type*):= List ι -- note not [List.Insert]
omit [Fintype α] [Fintype β]
def stood (x:Site n) (i:Point α): Leaf n α:= (x+wrap n i.1,i.2)
def paid {ι:Type*} (x:ι→ℝ)(S:Slip ι):= (List.map x S).prod
def invoice (z:Site n) (S:Slip (Point α)) : rule α n→ℝ := fun x=> paid x (S.map (stood z))
def meter (S:Slip (Point α)):= (S.map (fun i=>size i.1)).sum

lemma invoice_nil (z:Site n): invoice (α:=α) z []=fun _=>1:=by rfl
lemma invoice_cons (z:Site n) (S:Slip (Point α))(f:Point α): invoice z (f::S)=(fun x=> x (stood z f)) * invoice z S:=rfl
lemma invoice_add (z:Site n) (S T:Slip (Point α)): invoice z (S++T)= invoice z S *invoice z T:=by ext1 i; simp [invoice,paid]
lemma meter_add (S T:Slip (Point α)): meter (S++T)= meter S+meter T:= by simp [meter]
end YM.AllOrder.Ink
