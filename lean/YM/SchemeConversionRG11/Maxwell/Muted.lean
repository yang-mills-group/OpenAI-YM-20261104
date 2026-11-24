import YM.SchemeConversionRG11.Maxwell.Completes

/-! # Kernel stable under arbitrary colored-metric contractions. Can test just by
prepending the quadratic probes in any order. No field-horizon assumption. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Wick Tensor Set MvPolynomial
open scoped BigOperators ComplexOrder

variable {G : Gauge} {n m k l : ℕ} {ι : Type*} [Fintype ι] {X : Points n}

/-- Extensible spectators. -/
def Matches (e : Fin n ↪ Fin m) (W : Panel ι n G) (V : Panel ι m G) (S : Fin m → Flavor 0) : Prop :=
  (∀ i t, V i (e t)=W i t) ∧ ∀ j, (∀ t,e t≠j) → ∀ i,V i j=team G (S j) (S j)

def Muted (p : ι → ℂ) (W : Panel ι n G) :=
  ∀ (m : ℕ) (e : Fin n ↪ Fin m) (V : Panel ι m G) (S : Fin m → Flavor 0), Matches e W V S → ∀ X : Points m, X∈conf m →
    ∑ i:ι,p i*moment G X (V i)=0

def roll {n : ℕ} : Fin n ↪ Fin (n+1) := ⟨Fin.succ,Fin.succ_injective _⟩
lemma tumble {e : Fin n ↪ Fin m} {W : Panel ι n G} {V : Panel ι m G} {S : Fin m → Flavor 0} (h : Matches e W V S) (u : Flavor 0) :
    Matches (e.trans roll) W (stackAux u V) (Fin.cons u S) := by
  constructor
  · exact fun i t ↦ h.1 i t
  intro j; refine Fin.cases ?_ (fun j ↦ ?_) j
  · exact fun _ _ ↦ rfl
  exact fun he i ↦ h.2 j (fun t ht ↦ he t (congr_arg Fin.succ ht)) i
lemma muted_direct {p : ι→ℂ} {W : Panel ι n G} (h : Muted p W) (hx : X∈conf n) : ∑ i:ι,p i*moment G X (W i)=0 :=
  h _ (Embedding.refl _) W 0 ⟨fun _ _ ↦ rfl, fun _ hh ↦ (hh _ rfl).elim⟩ _ hx

/-- One metric link. -/
def pass (D : Echo k) (E : Echo l) (a b : Fin n) (W : Panel ι n G) : Panel (ι × G.ColorIndex) n G := fun i ↦ hit E i.2 b (hit D i.2 a (W i.1))

lemma hit_agrees {e : Fin n ↪ Fin m} {W : Fin n → WickPol G} {V : Fin m → WickPol G} (h : ∀ i,V (e i)=W i) (D : Echo k) (a : Fin n) (j : G.ColorIndex) (t : Fin n) :
    hit D j (e a) V (e t)=hit D j a W t := by
  unfold hit; rcases eq_or_ne t a with rfl|hh; · rw [update_self,update_self,h]
  rw [update_of_ne (e.injective.ne hh),update_of_ne hh,h]
lemma passes {e : Fin n ↪ Fin m} {W : Panel ι n G} {V : Panel ι m G} {S : Fin m → Flavor 0} (h : Matches e W V S) (D : Echo k) (E : Echo l) (a b : Fin n) :
    Matches e (pass D E a b W) (pass D E (e a) (e b) V) S := by
  refine ⟨fun i t ↦ hit_agrees (hit_agrees (h.1 i.1) D a i.2) E b i.2 t,?_⟩
  intro j he i; unfold pass hit; rw [update_of_ne (he b).symm,update_of_ne (he a).symm]; exact h.2 j he i.1
lemma Matches.uniq {e : Fin n ↪ Fin m} {W : Panel ι n G} {U V : Panel ι m G} {S : Fin m → Flavor 0} (h : Matches e W U S) (g : Matches e W V S) : U=V := by
  funext i j; by_cases he : ∃ t, e t=j
  · obtain ⟨v,rfl⟩ := he; rw [h.1,g.1]
  have he : ∀ t,e t≠j := not_exists.mp he; rw [h.2 j he,g.2 j he]
lemma Matches.exists (e : Fin n ↪ Fin m) (W : Panel ι n G) (S : Fin m → Flavor 0) : ∃ U, Matches e W U S := by
  refine ⟨fun i ↦ extend e (W i) fun j ↦ team G (S j) (S j),fun i t ↦ ?_, fun j hh i ↦ ?_⟩
  · dsimp only; rw [e.injective.extend_apply]
  unfold extend; dsimp only; rw [dif_neg (not_exists.mpr hh)]

theorem muted_pass (C₀ : G.ColorIndex) {W : Panel ι n G} {p : ι → ℂ} (h : Muted p W) (D : Echo k) (E : Echo l) (a b : Fin n) :
    Muted (fun i : ι×G.ColorIndex ↦ p i.1) (pass D E a b W) := by
  intro m e V S hh x hx
  obtain ⟨U,hU⟩ := Matches.exists e W S
  rw [Matches.uniq hh (passes hU D E a b),Fintype.sum_prod_type]
  have he := triple_assay C₀ p U (fun X hX r s t ↦ h _ _ _ _ (tumble (tumble (tumble hU r) s) t) _ hX) hx (e a) (e b) D E
  unfold payable at he; simp only [pay_hits] at he; exact he
end YM.SchemeConversionRG11.Corona
