import YM.RG17.Profile
import YM.RG17.Ledger

/-!
Local powers and spatial powers. Weighted scopes (smooth superbounds);
report propagation pays genuinely uniform constants for a profile family.
Domain at reporting scale from L,Z. No changing coefficients when cutting
at lower order. Estimates here are absolute, *not* quotient-representation
choices in a local error contract.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set OPE Extraction
open SharpGram.Allow
open scoped Topology BigOperators Classical

structure Scope (A:Type*) where
   pay : ℕ → A → ℝ → Prop
   nonneg {d x b} : pay d x b → 0≤b
   more {e d x b} : e ≤ d → pay d x b → pay e x b
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Spec.Final C f S}
    {L:Layout F} (Z:Ledger L) {n:ℕ} (K:Set (Points n))

def wears : Scope Unit:=⟨fun _ _ b=> 1≤b,fun h=>zero_le_one.trans h,fun _ h=> h⟩
def jointTests : Scope (Test n) where
    pay j ψ A:= tsupport ψ⊆K∧Demand j ψ A
    nonneg h:=h.2.nonneg
    more hh p:=⟨p.1,p.2.fewer hh⟩
def joins (I:Type*) : Scope (I × Test n) where
    pay j x A:=tsupport x.2⊆K∧Demand j x.2 A
    nonneg h:=h.2.nonneg
    more hh p:=⟨p.1,p.2.fewer hh⟩

variable {A: Type*} (u:Scope A) {E E':Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']

def Cost (e:ℕ) (y:ℝ→ A → E) : Prop := ∃ (C₀:ℝ) (j t:ℕ), 0≤C₀ ∧ ∀ᶠ r in home,∀ x A, u.pay t x A →
     ‖y r x‖≤ C₀*Z.g r^e * Z.Λ r^j * A
abbrev Bare (Z:Ledger L) (e:ℕ) (y:ℝ→ E) := Cost Z wears e (fun r _=>y r)

lemma Cost.uniform (ι:Type*) (w: Scope ι) (φ:ι→ A) (hx:∀ (x:ι) (j:ℕ) (a:ℝ), w.pay j x a → u.pay j (φ x) a) {e:ℕ} {y:ℝ→ A→ E} (h:Cost Z u e y) : Cost Z w e (fun r x=>y r (φ x)):=by
   obtain ⟨c,j,t,hc,H⟩:= h; exact ⟨c,j,t,hc,H.mono fun r hr x a ha=>hr _ _ (hx _ _ _ ha)⟩
namespace Cost
variable {Z u} {y z : ℝ→A→E} {e p:ℕ}
lemma transfer {z:ℝ→A→E'} (h : Cost Z u e y) (hx:∀ᶠ r in home,∀ x, ‖z r x‖ ≤ ‖y r x‖) : Cost Z u e z:=by
    obtain ⟨c,j,t,hc,H⟩:= h; exact ⟨c,j,t,hc,(H.and hx).mono fun r hr x a ha=>(hr.2 x).trans (hr.1 _ _ ha)⟩
lemma equal (h:Cost Z u e y) (t':ℕ) (hx:∀ᶠ r in home,∀ x a,u.pay t' x a → y r x=z r x) : Cost Z u e z:=by
    obtain ⟨c,j,t,hc,H⟩:= h; refine ⟨c,j,max t t',hc,(H.and hx).mono fun r hr x a ha=>?_⟩
    rw [← hr.2 _ _ (u.more (le_max_right ..) ha)]; exact hr.1 x a (u.more (le_max_left ..) ha)
lemma congr (h:Cost Z u e y) (he:∀ᶠ r in home, ∀ x,y r x=z r x):Cost Z u e z := h.transfer (he.mono fun r hr x=> (congr_arg norm ((hr x).symm)).le)
lemma zero (Z:Ledger L) (u:Scope A)(j:ℕ) (E:Type*)[NormedAddCommGroup E] : Cost Z u j (fun _ _ => (0:E)):= ⟨0,0,0,le_rfl, Eventually.of_forall fun _ _ _ _ => by simp⟩
lemma lesser (h:Cost Z u p y) (hp:e ≤ p) : Cost Z u e y:=by
    obtain ⟨c,j,t,hc,H⟩:= h; refine ⟨c,j,t,hc,(H.and Z.small).mono fun r hr x a ha=>?_⟩
    apply le_trans (hr.1 _ _ ha); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (Z.positive r).le hr.2 hp) hc) (pow_nonneg (zero_le_one.trans (Z.above r)) _)) (u.nonneg ha)
lemma add (h: Cost Z u e y) (he:Cost Z u e z) : Cost Z u e (fun r x=> y r x+z r x):=by
    obtain ⟨c,j,t,hc,H⟩:= h; obtain ⟨a,i,T,ha,Y⟩:= he
    let l:=max t T; refine ⟨c+a,max j i,l,add_nonneg hc ha,?_⟩
    filter_upwards [H,Y] with r hr hz x b hb
    have ht r:=Z.positive r
    have hb':= u.nonneg hb; simp_rw [add_mul]; apply (norm_add_le ..).trans (add_le_add _ _)
    · exact (hr x b (u.more (le_max_left t T) hb)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Z.above r) (le_max_left ..)) (by positivity)) hb')
    exact (hz x b (u.more (le_max_right t T) hb)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Z.above r) (le_max_right ..)) (by positivity)) hb')
lemma sub (h: Cost Z u e y) (he:Cost Z u e z) : Cost Z u e (fun r x=> y r x-z r x):=by
    have hn:Cost Z u e (fun r x=> -z r x):= he.transfer (Eventually.of_forall fun r x=> (norm_neg ..).le)
    exact (h.add hn).congr (Eventually.of_forall (fun r x=> (sub_eq_add_neg ..).symm))
lemma sum {J:Type*} {H:Finset J} {k:J→ℝ→A→E} (hc:∀ j∈H, Cost Z u e (k j)) : Cost Z u e (fun r x=> ∑ j∈H,k j r x):=by
    induction H using Finset.induction_on with
    | empty=> simpa using Cost.zero Z u e E
    | insert i s hi ih=> rw [Finset.forall_mem_insert] at hc; simpa only [Finset.sum_insert hi] using! hc.1.add (ih hc.2)
lemma incurs (h: Cost Z u e y) (a:A) (H:∀ t:ℕ,∃ b:ℝ,u.pay t a b) : Bare Z e (fun r=> y r a) := by
    obtain ⟨c,j,t,hc,h⟩:= h; obtain ⟨b,hb⟩:= H t
    refine ⟨c*b,j,0,mul_nonneg hc (u.nonneg hb),h.mono fun r hr x b' hb'=> ?_⟩
    have hz:= Z.positive r; have hl:=zero_le_one.trans (Z.above r); have hp:=u.nonneg hb
    exact (hr _ _ hb).trans ((le_of_eq (show c * Z.g _ ^ e * Z.Λ r ^ j * b = c*b * Z.g r ^ e * Z.Λ r ^ j by ring)).trans (le_mul_of_one_le_right (by positivity) hb'))
lemma coarse {b:ℝ} (hz:b<0) (e:ℕ) (B:ℝ→ℝ) (he:RateLE home OPE.run B b) (k:ℕ)
    (hx:∀ᶠ r in home,∀ x A,u.pay k x A → ‖y r x‖≤ B r*A) : Cost Z u e y:=by
    refine ⟨1,0,k,zero_le_one,?_⟩
    filter_upwards [hx,(Z.coarse_g.power e).outweigh he (by simpa using hz) ageLarge] with r hr hu x A hA
    rw [pow_zero,mul_one,one_mul]; exact (hr _ _ hA).trans (mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans hu) (u.nonneg hA))
lemma bound_single {x:ℝ→ E} (h:Bare Z e x): ∃ c:ℝ,∃ j:ℕ,0≤c∧∀ᶠ r in home, ‖x r‖≤ c*Z.g r^e* Z.Λ r^j:=by
    obtain ⟨c,j,t,hc,H⟩:= h; exact ⟨c,j,hc,H.mono (fun r hr=> by simpa only [mul_one] using hr () 1 le_rfl)⟩
lemma insert_single {x:ℝ→ E} (c:ℝ)(j:ℕ)(hc:0≤c)(h:∀ᶠ r in home, ‖x r‖≤ c*Z.g r^e * Z.Λ r^j) :Bare Z e x := by
    refine ⟨c,j,0,hc,h.mono fun r hr _ A hA=> ?_⟩; exact hr.trans (le_mul_of_one_le_right ((norm_nonneg _).trans hr) hA)
lemma bareProduct {V:Type*}[NormedAddCommGroup V] {M:ℝ→E'}
    (h:Bare Z p M) (hx:Cost Z u e y) {z:ℝ→A→V} (he:∀ᶠ r in home,∀ x, ‖z r x‖ ≤ ‖M r‖* ‖y r x‖) : Cost Z u (p+e) z:=by
    obtain ⟨c,j,hc,H⟩:= bound_single h; obtain ⟨d,i,t,hd,hM⟩:= hx
    refine ⟨c*d,j+i,t,mul_nonneg hc hd,?_⟩; filter_upwards [H,hM,he] with r hr hk hf x b hb
    exact ((hf _).trans (mul_le_mul hr (hk _ _ hb) (norm_nonneg _) ((norm_nonneg _).trans hr))).trans_eq (by simp_rw [pow_add]; ring)
lemma op [NormedSpace ℂ E][NormedSpace ℂ E'] {M:ℝ→E→L[ℂ] E'} (h:Bare Z p M) (hx:Cost Z u e y) : Cost Z u (p+e) (fun r x=> M r (y r x)):=
    bareProduct h hx <| Eventually.of_forall fun r _ => (M r).le_opNorm _
lemma capture (h:Cost Z u e y) [NormedSpace ℂ E][NormedSpace ℂ E'] (M:E→L[ℂ]E') : Cost Z u e (fun r x=>M (y r x)) :=by
    have hp:Bare Z 0 (fun _=>M):=insert_single ‖M‖ 0 (norm_nonneg _) (Eventually.of_forall fun _=>by simp)
    simpa only [zero_add] using op hp h
end Cost
end YM.RG17
