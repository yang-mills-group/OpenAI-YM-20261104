import YM.XSpace.Deck

/-!
# Correl frames & operator formal perturbative power-series action

Output type through horizon interpreted coefficientwise. Summands
include unread **correlations** coefficients with the fields interpreted
at formal parameters. This is changing frame not resetting coupling!
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory PowerSeries Finset
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d l n:ℕ} {E:Type} [AddCommMonoid E] [Module ℂ E]
abbrev Reports (G:Gauge) (d:ℕ):= ℕ→ Prediction G d
abbrev Days (n:ℕ):= Option (Fin n)→₀ ℕ
def tally (l n:ℕ): Finset (Days n):= Finset.finsuppAntidiag univ l
lemma totaled (x:Days n): x∈tally l n ↔ ∑ i,x i=l:=by simp [tally]
abbrev pulseU (l:Days n) (T:Guard G d) (v:Fin n→Sec G d): Fin n→Sec G d:= fun i=> coeff (l (some i)) T (v i)
def realm (T:Guard G d) (R: ℕ→ Correl G d E) : ℕ→ Correl G d E:= fun l n=> ∑ a∈ tally l n, loaded (fun i=> coeff (a (some i)) T) (R (a none) n)
lemma really (P:Guard G d) (R:ℕ→ Correl G d E) (t:Test n) (v:Fin n→Sec G d): realm P R l n t v=∑ a∈ tally l n,R (a none) n t (pulseU a P v):=by simp only [realm,LinearMap.sum_apply,_root_.sum_apply,loads]
lemma rest (P:Guard G d) (R:ℕ→ Correl G d E): realm P R 0=recruit (coeff 0 P) (R 0):=by ext n t p; rw [really,tally, finsuppAntidiag_zero,sum_singleton]; rfl

lemma tail_free (X: Guard G (d+1)) (Y:Guard G d) (H : ∀ n p, coeff n X (step d p)=step d (coeff n Y p)) (R:ℕ→Correl G (d+1) E) (l:ℕ): recruit (step d) (realm X R l)= realm Y (fun j=> recruit (step d) (R j)) l:= by
  ext n t p; rw [recruits,really,really]; apply sum_congr rfl; intro a _; rw [recruits]; apply congr_arg; ext1 i; exact H ..
private lemma tally_le {a:Days n} (h:a∈tally l n) (i): a i≤l:=((totaled a).mp h) ▸ single_le_sum (f:=fun j=>a j) (fun _ _=> Nat.zero_le _) (mem_univ i)
private lemma solo {a:Days n} (h:a∈tally l n) (i) (H:a i=l): a= Finsupp.single i l:=by
  ext1 j; by_cases hv:j=i; · subst j; rw [Finsupp.single_eq_same,H]
  rw [Finsupp.single_eq_of_ne hv]
  have hh : ∑ k∈univ.erase i,a k=0:= by have he:= add_sum_erase (univ:Finset (Option (Fin n))) (fun j=> a j) (mem_univ i); rw [(totaled a).mp h,H] at he; omega
  exact (sum_eq_zero_iff_of_nonneg (fun k _=>Nat.zero_le (a k))).mp hh j (mem_erase.mpr ⟨hv,mem_univ _⟩)
def jumpDay (n l:ℕ) : Fin n→Days n:= fun i=> Finsupp.single (some i) l
lemma jumping (i:Fin n): jumpDay n l i∈tally l n:=by
  rw [totaled,sum_eq_single (some i)]; exact Finsupp.single_eq_same; intro b _ hb; exact Finsupp.single_eq_of_ne hb; simp
lemma jumper (h:l≠0):Injective (jumpDay n l):=by
  intro a b he; by_contra h'; apply h; rw [← show jumpDay n l a (some a)=l from Finsupp.single_eq_same, he]; exact Finsupp.single_eq_of_ne (fun hc=>h' (Option.some.inj hc) )
lemma drift (x:Guard G d) (p:Fin n→Sec G d) (i : Fin n): pulseU (jumpDay n l i) x p= update ( ((coeff (R:=FieldEnd G d) 0) x : FieldEnd G d) ∘ p) i (coeff l x (p i)):=by
  ext1 j; by_cases hv:j=i; · subst j; simp only [pulseU,jumpDay,Finsupp.single_eq_same, update_self]
  simp [pulseU,jumpDay,Finsupp.single_eq_of_ne,hv]
private lemma costs_off {r:Days n} (h:r∈tally l n) {a:Fin n} (ht:r≠jumpDay n l a): r (some a)<l:= lt_of_le_of_ne (tally_le h _) (fun he=> ht (solo h _ he))
-- through a fixed positive order use computation comparison before that degree. A mismatch at top field coefficient contributes only tangent.
theorem deviates (P Q:Guard G d) (R:Reports G d) (hl:l≠0) (h:∀ i<l,coeff i P=coeff i Q) : realm P R l-realm Q R l=tang (coeff 0 Q) (coeff l P - coeff l Q) (R 0):=by
  ext1 n; ext1 t; ext1 v; change realm P R l n t v-realm Q R l n t v=tang _ _ _ n t v
  rw [really,really,← sum_sub_distrib,touches]
  let a (i: Days n):ℂ:= R (i none) n t (pulseU i P v)- R (i none) n t (pulseU i Q v); let g:=jumpDay n l; let u:=Finset.univ.image g; change ∑ i∈tally l n,a i=_
  have hv:u⊆ tally l n:= fun x hx=>by obtain ⟨i,_,rfl⟩:= Finset.mem_image.mp hx; exact jumping ..
  rw [← sum_subset hv (f:=a) ?_,sum_image (f:=a) (s:=Finset.univ) (g:=g) ((jumper hl).injOn)]; swap
  · intro i hi hp; unfold a; apply sub_eq_zero.mpr; apply congr_arg; funext j; unfold pulseU; rw [h _ (costs_off hi (a:=j) (fun he=> hp (he.symm ▸ mem_image_of_mem g (mem_univ j))))]
  refine sum_congr rfl fun i _=>?_
  unfold a g; simp_rw [drift,h 0 (Nat.pos_of_ne_zero hl), jumpDay, Finsupp.single_eq_of_ne (show none ≠ some i from (Option.some_ne_none _).symm), LinearMap.sub_apply,MultilinearMap.map_update_sub]

lemma knows (P Q:Guard G d) (R:ℕ→Correl G d E) (h:∀ i≤l,coeff i P=coeff i Q): realm P R l=realm Q R l:=by
  ext n t v; rw [really,really]; refine sum_congr rfl (fun x hx=>?_); apply congr_arg; funext i; unfold pulseU; rw [h _ (tally_le hx _)]
lemma nest (T:Pick G (d+1)) (U: Pick G d) (he:∀ j,fell d (T j)=U j) : ∀ j p, coeff j (deck T) (step d p)=step d (coeff j (deck U) p):=by
  intro j p; rw [decked,decked,pulling,pulling,← he]; split_ifs
  · exact stoop ..
  exact (fells ..).symm
end YM.XSpace.Normalize
