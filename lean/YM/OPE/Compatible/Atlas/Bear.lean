import YM.OPE.Compatible.Atlas.Illuminate
/-!
# Compiler: when an expression is made from separated products, with exterior offsets finite (may depend on a side index), and demands all sampled directions; failures don't accrue separately in budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Boundary EveryPhase
open scoped Topology BigOperators Classical
variable {X V:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){Q:Finset X}
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U: Spec.Final C F S}
variable {ψ:Filter V}{T u p: V→ℝ} {s: V→X→ℝ} {A:Circuit U X V}{a b:V→(X→ E4)→ℂ}
-- min gaps exponential: uniform constant specified up front for all recordable here. perturbed too. with M slack
variable {η r c :ℝ}
def Auth (D:Origin X)(Q:Finset X)(ψ:Filter V)(T:V→ℝ)(s:V→X→ℝ)(η r c:ℝ)(A:Circuit U X V)(a:V→ (X→E4)→ℂ):Prop:= ∀ᶠ i in ψ, ∀ x:X→ E4,Ridge (s i) η r D Q x → A.value i x=a i x∧∀ b∈ A.atoms,b.Quota D Q (s i) i x η (Real.exp (-c*T i))
-- perturb eta=M+1. Ridge monotone ensures uses slightly looser b=[half].
structure Burst (D:Origin X)(Q:Finset X)(ψ:Filter V)(T:V→ℝ)(s:V→ X→ℝ) : Prop where
    fresh (η:ℝ) : 0<η→ Glowing D Q ψ T s η
    fronts : ∀ᶠ i in ψ,∀ x∈Q, Real.exp (-T i) ≤ s i x
lemma Burst.crown (h: Burst D Q ψ T s): Crown Q:= (h.fresh 1 one_pos).crowned
lemma Burst.life (h: Burst D Q ψ T s): Tendsto T ψ atTop:= (h.fresh 1 one_pos).ray
lemma Ridge.relaxed {s:X→ℝ} {x:X→ E4} (hx:Ridge s η r D Q x)(hη:0 ≤ η)(hp:Bright Q s)(he:Crown Q):Ridge s (η/2) (r+1) D Q x:=by
    refine ⟨hx.belly,fun a b ha hb hv=> (hx.near a b ha hb hv).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (hp.pos a ha).le),fun a b ha hb hv ht=>?_⟩
    exact (mul_le_mul_of_nonneg_right (by linarith only [hη] : η/2 ≤ η) (hp.pos _ (diverge D he ha hv)).le).trans (hx.span a b ha hb hv ht)
lemma Auth.encode (L:Allot C)(hG:G.Simple)(H:Burst D Q ψ T s) {B:ℕ} {w:ℝ}(hw:∀ᶠ i in ψ,0 ≤ u i∧ u i ≤Real.exp (w*T i)) (h:Auth D Q ψ T s (η/2) (r+1) c A a)(hc:0<c)(hη:0<η)(hq:Score ψ T p)(hf:∀ᶠ i in ψ,∀ x:X→E4, Ridge (s i) (η/2) (r+1) D Q x → Screened D Q C x (aperture D C B 2 (η/2) (T i) (s i)) → u i * ‖a i x‖ ≤ p i) : ∃ f:V→ℝ, Score ψ T f∧ ∀ᶠ i in ψ,∀ x:X→ E4, Ridge (s i) η r D Q x → u i * ‖a i x‖ ≤ f i:=by
    have hq₀:0<η/2:=by positivity
    obtain ⟨f,hs,hF⟩:= illuminated (A:=A) D L hG (H.fresh _ hq₀) hq hq₀ hc hw (B:=B) (M:=r) ((hf.and h).mono (fun i hi x hx ho=> (hi.2 x hx).1.symm ▸ hi.1 x hx ho))
    refine ⟨f,hs,?_⟩; filter_upwards [time_bright D (H.fresh η hη)|>.lit,hF,h] with i hp hh hK x hx; obtain ⟨hy,he⟩:= hK x (Ridge.relaxed D hx hη.le hp (Burst.crown D H)); rw [← hy]; exact hh _ hx he
namespace Auth
-- closed under polynomial operations (phase ray inserted by atom compiler)
lemma ground {z:ℂ} : Auth D Q ψ T s η r c (Circuit.base (U:=U) z) (fun _ _=> z):=Eventually.of_forall fun _ _ _=>⟨rfl,fun _ h=>by simp [Circuit.atoms] at h⟩
lemma addition (h: Auth D Q ψ T s η r c A a){Y:Circuit U X V}(hp:Auth D Q ψ T s η r c Y b) : Auth D Q ψ T s η r c (A.plus Y) (fun i x=>a i x + b i x):= (h.and hp).mono (fun _ hi x hx=>⟨congr_arg₂ _ (hi.1 x hx).1 (hi.2 x hx).1,fun _ hu=> (Finset.mem_union.mp hu).elim ((hi.1 x hx).2 _) ((hi.2 x hx).2 _)⟩)
lemma multiplication (h: Auth D Q ψ T s η r c A a){Y:Circuit U X V}(hp:Auth D Q ψ T s η r c Y b) : Auth D Q ψ T s η r c (A.times Y) (fun i x=>a i x*b i x):= (h.and hp).mono (fun _ hi x hx=>⟨congr_arg₂ _ (hi.1 x hx).1 (hi.2 x hx).1,fun _ hu=> (Finset.mem_union.mp hu).elim ((hi.1 x hx).2 _) ((hi.2 x hx).2 _)⟩)
-- point star? not needed yet
end Auth
-- spec consumed univ classical
def Scannable (U:Spec.Final C F S)(D:Origin X)(Q:Finset X)(ψ:Filter V)(T:V→ℝ)(s:V→X→ℝ)(η r c:ℝ)(a:V→ (X→E4)→ℂ):Prop:=∃ A:Circuit U X V, Auth D Q ψ T s η r c A a
namespace Scannable
lemma constant (t:ℂ): Scannable U D Q ψ T s η r c (fun _ _=> t):= ⟨.base t,Auth.ground D⟩
lemma sum (h: Scannable U D Q ψ T s η r c a)(hp:Scannable U D Q ψ T s η r c b): Scannable U D Q ψ T s η r c (fun i x=> a i x+b i x):=h.elim fun _ h=> hp.elim fun _ hp=>⟨_,Auth.addition D h hp⟩
lemma mul (h: Scannable U D Q ψ T s η r c a)(hp:Scannable U D Q ψ T s η r c b): Scannable U D Q ψ T s η r c (fun i x=> a i x*b i x):=h.elim fun _ h=> hp.elim fun _ hp=>⟨_,Auth.multiplication D h hp⟩
lemma shift (h:Scannable U D Q ψ T s η r c a)(ht:∀ᶠ i in ψ, ∀ x:X→ E4,Ridge (s i) η r D Q x → a i x=b i x): Scannable U D Q ψ T s η r c b:=by
   obtain ⟨A,h⟩:=h; exact ⟨A,(h.and ht).mono (fun i hi x hx=> ⟨(hi.1 x hx).1.trans (hi.2 x hx),(hi.1 x hx).2⟩)⟩
lemma sub (h: Scannable U D Q ψ T s η r c a)(hp:Scannable U D Q ψ T s η r c b): Scannable U D Q ψ T s η r c (fun i x=> a i x-b i x):=shift D (sum D h (mul D (constant D (-1:ℂ)) hp)) (Eventually.of_forall fun _ _ _=> by ring)
lemma summons {T':Type*}(s':Finset T')(f:T'→ V→(X→ E4)→ℂ)(h:∀ i∈s', Scannable U D Q ψ T s η r c (f i)):Scannable U D Q ψ T s η r c (fun i x=>∑ j∈s',f j i x):=by
    induction s' using Finset.induction_on with
    | empty => simpa using (constant (U:=U) (s:=s) (Q:=Q) (ψ:=ψ) (T:=T) (c:=c) (η:=η) (r:=r) D 0)
    | insert i S he ih=> exact shift D (sum D (h i (Finset.mem_insert_self ..)) (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))) (Eventually.of_forall fun _ _ _=>by rw [Finset.sum_insert he])
end Scannable
end YM.OPE.Arboreal.Trace
