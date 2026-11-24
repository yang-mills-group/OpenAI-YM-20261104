import Mathlib.Algebra.Module.BigOperators
import YM.MS.DiscreteTrace

/-! # Free master test on any momentum group

Test the commutation in mode amplitudes, before using any volume/sampling
normalization. Needed even if identities are then in an approximation to a trace.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Set Finset Koszul Flux
variable {A P R : Type*} [AddCommGroup P] [CommRing R] [Fintype A] {p : Sector A}

/-- q matrix is *backwards*: `table a i q` acts on a symbol by replacing
 an input letter of type i with output a. Enforced opposite parity. -/
structure Charge (p : Sector A) (P R : Type*) [Zero R] where
    table : A → A → P → R
    from_opposite (a b : A) (q:P) : table a b q ≠ 0 → p b = !(p a)
namespace Charge
variable (Z : Charge p P R) (F : Row A P R)
def travel (q:P) : A ↪ Mode A P := ⟨fun a => (a,q), fun _ _ h => congr_arg Prod.fst h⟩
def transfer (p : Sector A) (i:A) := (Finset.univ (α:=A)).filter fun u=> p u = !(p i)
def move : Shift R (field p (P:=P)) true := {
    source l:= (transfer p l.1).map (travel l.2)
    mat i j:= Z.table i.1 j.1 i.2
    row a x h:= by obtain ⟨i,hi,rfl⟩:=mem_map.mp h; simpa [transfer,field,travel] using (mem_filter.mp hi).2 }
def raise : Op (Mode A P) R := Z.move.Q

omit [AddCommGroup P] in
lemma hook_rule (a:A) q : Z.move.hook (a,q) F = ∑ b:A,Z.table a b q • D (b,q) F := by
    simp only [Shift.hook,move, LinearMap.sum_apply,LinearMap.smul_apply, Finset.sum_map, travel, Function.Embedding.coeFn_mk]
    exact Finset.sum_subset (Finset.filter_subset ..) fun b hb h=> by
       have he : Z.table a b q=0:= Classical.byContradiction fun hh=> h (mem_filter.mpr ⟨hb,Z.from_opposite a b q hh⟩)
       simp [he]
omit [AddCommGroup P] in
lemma act_at (a:A) q w : Z.raise F ((a,q)::w) = (∑ i:A, Z.table a i q * F ((i,q)::w))+cross true (p a)* Z.raise (D (a,q) F) w := by
    rw [D_eval _ (Z.raise F), raise, Z.move.deriving', hook_rule]; simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, at_D]
-- move hook doesn't change external momentum
lemma agree_at {a:P} {F G : Row A P R} (h : ∀ w, net w=a → F w=G w) : ∀ w, net w=a → Z.raise F w=Z.raise G w := by
    intro w hv; induction w generalizing F G a with
    | nil=> simp [raise]
    | cons i w IH=>
       rcases i with ⟨l,q⟩; rw [act_at,act_at]; refine congr_arg₂ _ (sum_congr rfl fun i _=>?_) (congr_arg _ (IH (a:=net w) ?_ rfl))
       · rw [h _ (by simpa using hv)]
       · intro u he; exact h _ (by simpa only [net_cons,he] using hv)
lemma conserve (h : Conserved F) : Conserved (Z.raise F) := by
  intro i hi; refine (Z.agree_at (G:=0) (a:=net i) (fun j he=> h j (he ▸ hi)) i rfl).trans ?_; simp

/-- Row equation in matrix form. -/
def change (K : Flux A P R) : Flux A P R := fun a e q =>
    (∑ i:A, K i e q * Z.table i a q)+ (∑ j:A,cross true (p a)*(K a j q * Z.table j e (-q)))
section
variable {F}
-- ordered row supports without sym averaging
lemma doubles (a e:A) q (h : p e=p a) : diffPair (a,q) (e,-q) (Z.raise F) = Z.raise (diffPair (a,q) (e,-q) F)+
     (∑ i:A, Z.table a i q • diffPair (i,q) (e,-q) F) + (∑ j:A, (cross true (p a)*Z.table e j (-q)) • diffPair (a,q) (j,-q) F):=by
    unfold raise; simp only [diffPair_apply,Shift.deriving',hook_rule,map_add,map_sum,map_smul,field,smul_add,smul_smul,h,cross_cross, one_smul,Finset.smul_sum]
    abel
lemma commutes (K : Flux A P R) (h : closed K p false) (q) : Z.raise (trc K q F)+trc (change Z K) q F = trc K q (Z.raise F) := by
    simp only [trc, LinearMap.sum_apply, LinearMap.smul_apply,map_sum,map_smul];
    have he a e : K a e q • diffPair (a,q) (e,-q) (Z.raise F)= K a e q • (Z.raise (diffPair (a,q) (e,-q) F)+
     (∑ i:A, Z.table a i q • diffPair (i,q) (e,-q) F) + (∑ j:A, (cross true (p a)*Z.table e j (-q)) • diffPair (a,q) (j,-q) F)) := by
      by_cases hh:K a e q=0; simp [hh]; rw [Z.doubles a e q]; simpa using h a e q hh
    simp_rw [he,smul_add,Finset.smul_sum,smul_smul,Finset.sum_add_distrib]
    unfold change; simp_rw [add_smul, sum_smul, Finset.sum_add_distrib]; rw [← add_assoc];
    congr 1
    · congr 1; nth_rw 1 [Finset.sum_comm (f:=fun a b => ∑ i:A, (K i b q * Z.table i a q) • diffPair (a,q) (b,-q) F)] -- check param
      nth_rw 1 [Finset.sum_comm (f:=fun a b => ∑ i:A, (K a b q * Z.table a i q) • diffPair (i,q) (b,-q) F)]
      apply sum_congr rfl; intro i _; rw [Finset.sum_comm]
    apply sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; rw [mul_left_comm]
lemma exchange (K : Flux A P R) (h : closed K p false) (s : Finset P) :
    Z.raise (slab K s F)+ slab (change Z K) s F=slab K s (Z.raise F) := by
    simp only [slab, LinearMap.sum_apply, map_sum, ← Finset.sum_add_distrib, Z.commutes K h]
end
end Charge
end YM.MS.Plane
