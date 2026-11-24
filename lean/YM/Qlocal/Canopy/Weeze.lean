import YM.Qlocal.Canopy.Deline
/-!
 # Coherence restricting to a chosen set of LOG factors.
 Still permits all roots/origin appellations. Expression.turn need hulls; this
 proof for perturbative prescription part. And restoring pole costs for Sluice.
 `RGComparison.Remainder.Staff.Germ` (another implementation, read on snapshot)
 independent compass inspiration for comb.W proofs; avoid importing.Check.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Canopy.Button
open Function Finset Filter Marker Merge Switch
open Comparison.RG02.Order Comparison.RG02.Cumulants Comparison.RG02.Assembly
open PertExtension PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP
open AllOrder.Response Extra.Trajectories Next.SectorChange
open scoped Topology ContDiff BigOperators Classical
variable {σ ι:Type} [Fintype ι] [Fintype σ]
variable {V:Type} [DecidableEq V]{R:Census V} {K:ι→Multi.Hot R} (L:σ ↪ ι)
lemma combPath (u v:Score ι)(A:Finset ι): comb 0 u v A=∑ i∈A.powerset,u i*v (A \ i):= by
 rw [RGComparison01.Slate.flesh,Fintype.sum_prod_type]; let f(i j:Finset ι):= if A=i∪j∧Disjoint i j then u i*v j else 0; have he i: ∑ j,f i j=if i ⊆ A then u i*v (A \ i) else 0:= by
   split
   next h=>
     rw [sum_eq_single (A \ i)]; · unfold f; rw [if_pos ⟨(union_sdiff_of_subset h).symm,Finset.disjoint_sdiff ..⟩]
     · intro b _ he; unfold f; apply if_neg; intro hx; apply he; rw [hx.1, union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hx.2.symm] -- union_sdiff_left?
     simp
   next h=> exact Finset.sum_eq_zero fun j _=> if_neg (fun (hx:A=i∪j ∧ Disjoint i j)=> h (hx.1.symm ▸ subset_union_left))
 change ∑ i,∑ j,f i j=_; simp_rw [he]; rw [← Finset.sum_filter]; apply Finset.sum_congr _ (fun i _=>rfl); ext i;simp
omit [Fintype ι] [Fintype σ] in
lemma power_contract (A:Finset σ): (A.map L).powerset=A.powerset.image (Finset.map L) := by rw [Finset.map_eq_image,powerset_image]; exact congr_arg (Finset.image · A.powerset) ((funext (Finset.map_eq_image L)).symm)
abbrev contracted (L:σ ↪ ι)(P:Book ι): Book σ:= fun j u=> P j (u.map L)
lemma contract_core (L:σ ↪ ι): contracted L (neutral ι)=neutral σ:= by
 ext1 i; unfold contracted neutral; by_cases h:i=0; swap; · rw [if_neg h]; exact funext fun j=> by rw [if_neg h]; rfl
 funext j; simp [h,Merge.Switch.bench]
lemma contract_plan (L:σ ↪ ι)(P Q:Book ι) : contracted L (pledge P Q)= pledge (contracted L P) (contracted L Q):= by
 ext1 i; ext s; unfold contracted pledge; rw [Finset.sum_apply, Finset.sum_apply]; apply Finset.sum_congr rfl; intro j _; rw [combPath,combPath,power_contract,sum_image]; · simp_rw [Finset.map_sdiff]
 exact fun i _ v _ hp=> Finset.map_injective L hp
lemma contract_order {k:ℕ}(L:σ ↪ ι)(P:Book ι) : contracted L (knot P k)=knot (contracted L P) k:= by induction k with
 | zero=>rw [knot,knot]; exact contract_core _
 | succ k ih=>rw [knot,knot,contract_plan,ih]
lemma contract_pass (k:ℕ)(L:σ ↪ ι)(P:Book ι) : contracted L (connect k P)=connect k (contracted L P):= by
 ext i t; have hx:neutral σ- contracted L P= contracted L (neutral ι - P):= (by rw [← contract_core L]; rfl); unfold connect; rw [hx]; simp_rw [← contract_order, contracted, Finset.sum_apply,Pi.smul_apply] -- incl binder `k` shadow.
lemma cross {k n:ℕ} {L:σ ↪ ι}(P:Book ι)(h:Grey (neutral σ - contracted L P))(hk:Fintype.card ι ≤ k)(hn:Fintype.card σ≤ n) : contracted L (connect k P)= connect n (contracted L P):= by rw [contract_pass, toll_free _ h (le_trans (Fintype.card_le_of_injective L L.injective) hk) hn]
local notation "T"=> Finset.map L
variable {A:Finset σ}
lemma pose_map : pose K (T A)=pose (K ∘ L) A:= Finset.prod_map ..
lemma fits_map (A:Finset σ) : Button.Ideal (K ∘ L) A ↔ Ideal K (T A):= by
 have hi(K:ι→ Multi.Hot R)(h:¬Button.Ideal K (T A))(hq: Button.Ideal (K ∘ L) A) : False:= burgeon _ hq ((pose_map L).symm.trans (spacer _ h))
 constructor; exact fun hp=> Classical.byContradiction (fun h=> hi _ h hp) -- want by_contra
 exact fun h=> Classical.byContradiction fun he=> burgeon K h ((pose_map L).trans (spacer _ he))
lemma pin_map (h: Ideal (K ∘ L) A): pin _ A h=pin K (A.map L) ((fits_map L A).1 h):= by
 let u:=pin (K∘ L) _ h; let v:= pin K _ ((fits_map L A).1 h); have he : Poly.send u 1=Poly.send v 1:= (spar _ h).symm.trans ((pose_map L).symm.trans (spar _ ((fits_map L A).1 h))); by_contra h'
 exact (one_ne_zero (α:=ℂ)) (by simpa [show u≠v from h'] using congr_arg (fun i:Poly R=> i.part u) he)
-- weight coherence vertically Book. Here inclination change lambda amplitudes pipeline.
def polish (K:ι→ℝ)(v:Score ι): Score ι:=fun i=>(∏ j∈i,K j)*v i
def polishP (K:ι→ℝ)(v:Book ι): Book ι:=fun i=>polish K (v i)
variable (K':ι→ℝ) (B:Book ι)
omit [Fintype σ]
lemma heal : polishP K' (neutral ι)= neutral ι:= by ext i p; by_cases hx:p=∅ <;> by_cases hi:i=0 <;> simp [polishP,polish,hx,neutral,hi,Merge.Switch.bench]
lemma healP (A:Score ι)(B:Score ι): polish K' (comb 0 A B)=comb 0 (polish K' A) (polish K' B):= by
 ext i; rw [combPath]; unfold polish; rw [combPath,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; let v₀:= i \ j; let w:=∏ k∈i,K' k; have h:w=(∏ k∈j,K' k)*(∏ k∈ i \ j,K' k):= by rw [← prod_union (Finset.disjoint_sdiff ..),union_sdiff_of_subset (mem_powerset.mp hj)]
 change w *_= _; rw [h]; ring
lemma heel (A:Book ι) : polishP K' (pledge A B)= pledge (polishP K' A) (polishP K' B) := by
 ext i v; unfold pledge polishP; simp_rw [← healP,Finset.sum_apply,polish,Finset.sum_apply,Finset.mul_sum]
lemma happy (i:ℕ) : polishP K' (knot B i)=knot (polishP K' B) i:=by induction i with
 | zero=>rw [knot,knot,heal]
 | succ i hi=> rw [knot,knot, heel, hi]
lemma hears (n:ℕ) : polishP K' (connect n B)=connect n (polishP K' B):= by
 have ht: neutral ι - polishP K' B=polishP K' (neutral ι - B):= by nth_rw 1 [← heal K']; ext i v; simp [polishP,polish,mul_sub]
 unfold connect; rw [ht]; ext i v; simp_rw [← happy,polishP,polish, Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]; exact sum_congr rfl (fun i _=>mul_left_comm ..)
end YM.Qlocal.Canopy.Button
