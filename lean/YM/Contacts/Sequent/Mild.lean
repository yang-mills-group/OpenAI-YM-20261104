import YM.Contacts.Tempo.Murk
import Mathlib.RingTheory.Polynomial.Pochhammer
/-! # PL observational cost calculus. Polynomial in chronological n on fixed lattice filter; measure location m(p) can be chosen, may make the polynomial coefficients look large; Shades means at the uniform parameters shown. -/
namespace YM.Contacts.Sequent
open Tempo Tempo.Grounds
open Function Set Filter Finset
open scoped Classical Topology BigOperators NNReal
noncomputable section
variable {ι κ X:Type}{m:κ→ℕ} {i j k l n:ℕ}{f g h:κ→ℕ→ℝ}{b:ℝ}
local notation "D" => chord
abbrev labor (f:κ→ℕ→ℝ)(n:ℕ) : κ→ℕ→ℝ:= fun p i=>f p (i+n)
def Harbor (m:κ→ℕ)(f:κ→ℕ→ℝ):Prop:= Rates m f ∧ ∃ n:ℕ,Shades m (D f n)
namespace Harbor
local notation "Ψ" => Harbor m
lemma carry (h:Shades m f):Ψ f:= ⟨h.road,0,h⟩
lemma given (v:ℝ):Ψ (fun _ _=> v):= ⟨Rates.constant (b:=‖v‖) (norm_nonneg _) (fun _ _=>le_rfl),1,(by simp only [chord,sub_self]; exact Shades.zero)⟩
lemma broad (h:Ψ f) : Rates m f:= h.1
lemma big (h:Shades m (D f i))(he:i≤ j): Shades m (D f j):= by obtain ⟨k,rfl⟩:= Nat.exists_eq_add_of_le he; clear he; induction k with|zero=>exact h|succ k ih=> rw [← Nat.add_assoc]; exact (ih.sun 1).minus ih
lemma succRoad (h:Rates m f): Rates m (D f 1):= (h.along 1).sub h
lemma fest (f:κ→ℕ→ℝ)(g:κ→ℕ→ℝ)(i:ℕ): D (f+g) i=D f i+D g i:= by induction i with|zero=>rfl|succ i ih=> funext p n; unfold chord; change (D (f+g) i p (n+1)- D (f+g) i p n)= _; rw [ih]; simp only [Pi.add_apply]; abel
lemma festival (i:ℕ): D (labor f j) i = labor (D f i) j:= by induction i with| zero=>rfl|succ i ih=> funext p n; change D (labor f j) i p _- D (labor f j) i p _= D f i p _-D f i p _; rw [ih]; unfold labor; congr 2 <;> omega
lemma festival_minus (i:ℕ):D (f-g) i=D f i - D g i:= by induction i with|zero=> rfl|succ i ih=> funext x n; unfold chord; simp only [Pi.sub_apply,ih]; abel
lemma laboring (h:Ψ f)(i:ℕ):Ψ (labor f i):= by obtain ⟨h,j,H⟩:=h; exact ⟨h.along _,j,(festival j).symm ▸ H.sun i⟩
lemma plus (h:Ψ f)(he:Ψ g): Ψ (fun p i=> f p i+g p i):= by obtain ⟨H,j,h⟩:=h; obtain ⟨U,k,he⟩:=he; refine (show Harbor m (f+g) from ⟨H.add U,j+k,?_⟩); rw [fest]; exact (big h (Nat.le_add_right j k)).plus (big he (Nat.le_add_left k j))
lemma minus (h:Ψ f)(he:Ψ g): Ψ (fun p i=> f p i-g p i):= by obtain ⟨H,j,h⟩:=h; obtain ⟨U,k,he⟩:=he; refine (show Harbor m (f-g) from ⟨H.sub U,j+k,?_⟩); rw [festival_minus]; exact (big h (Nat.le_add_right j k)).minus (big he (Nat.le_add_left k j))
lemma totaled {A:ι→κ→ℕ→ℝ}(s:Finset ι)(h:∀ i∈s,Ψ (A i)): Ψ (fun x n=>∑ i∈s,A i x n):= by induction s using Finset.induction with| empty=> simpa only [Finset.sum_empty] using (given (m:=m) 0)| insert i S hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih (fun v hv=> h v (mem_insert_of_mem hv)))
lemma chug (j:ℕ):D f (j+1)=D (D f 1) j:= by induction j with|zero=> rfl|succ j ih=> rw [chord,ih]; rfl -- ambiguity
lemma cruise (h:Ψ (D f 1))(hf:Rates m f) : Ψ f:= by obtain ⟨he,j,h⟩:= h; exact ⟨hf,j+1,(chug j).symm ▸ h⟩
lemma successor (h:Ψ f): Ψ (D f 1):= (h.laboring 1).minus h
lemma mul (h:Ψ f)(he:Ψ g):Ψ (fun p i=>f p i*g p i):= by
    have ht(z:ℕ):∀ (j k:ℕ), j+k=z →∀ f g:κ→ℕ→ℝ,Rates m f → Rates m g → Shades m (D f j) → Shades m (D g k) → Ψ (f*g):= by
       induction z using Nat.strong_induction_on with|h z ih=>
       rintro j k rfl f g h h' hj hk; by_cases hp:j=0; · subst j; exact carry ((show Shades m f from hj).mul h')
       by_cases hx:k=0; · subst k; rw [mul_comm]; exact carry ((show Shades m g from hk).mul h)
       let P:= D f 1; let Q:= D g 1; rw [show j=j-1+1 from by omega,chug] at hj; rw [show k=k-1+1 from by omega,chug] at hk -- destroys j?? expression hJ replaced
       have he:Shades m (D P (j-1)):= hj; have hv: Shades m (D Q (k-1)):=hk; have hu:Shades m (D f j):=(show j-1+1=j from by omega) ▸ ((chug (j-1)).symm ▸ hj); have hw:Shades m (D g k):= (show k-1+1=k from by omega) ▸ ((chug (k-1)).symm ▸ hk); let G:=labor g 1; refine cruise (?_) (h.mul h'); rw [show D (f*g) 1=P*G+f*Q from (by funext p i; change f p (i+1)*g p (i+1)-_= (f p (i+1)-f p i)*g p _+f p i*(g p (i+1)-g p i); simp only [chord,Pi.mul_apply]; ring)]; apply plus; exacts [ih (j-1+k) (by omega) (j-1) k rfl P G (succRoad h) (h'.along _) he (by unfold G; rw [festival]; exact hw.sun 1), ih (j+(k-1)) (by omega) j _ rfl f Q h (succRoad h') hu hv]
    obtain ⟨H,j,h⟩:=h; obtain ⟨U,k,he⟩:=he; exact ht _ j k rfl f g H U h he
lemma pow (h:Ψ f)(i:ℕ):Ψ (fun p n=> f p n ^ i):= by induction i with| zero=> simp_rw [pow_zero]; exact given _|succ i ih=> simp_rw [pow_succ]; exact ih.mul h
-- occasionally with no hypothesized growth, just know diff envelope:
lemma rates_by_metric {c:ℝ}(hc:0 ≤ c)(ht:∀ p, ‖f p (m p)‖≤ c)(h:Rates m (D f 1)): Rates m f:= h.neutral ht hc (fun x i=> by unfold chord; rw [one_mul]; simp only [chord]; ring)
lemma worth {c:ℝ}(hc:0≤c)(ht:∀ p,‖f p (m p)‖≤c)(h:Ψ (D f 1)):Ψ f:= cruise h (rates_by_metric hc ht h.broad)
end Harbor
end
end YM.Contacts.Sequent
