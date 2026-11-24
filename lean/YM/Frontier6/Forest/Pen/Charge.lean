import YM.Frontier6.Forest.Twins.Glow

/-!
# Tariff grammar on Spelling streams

All budget slopes refer to the same clock. As the program is *valuation-indexed*,
 subdivision into strict power scales, words, and reserves need not be uniform
 here. The rules are used through a separate argument to get ordinary epsilon
 estimates; they do not supply log-power (order-in-coupling independent) estimates.

One parent valuation at a time. Product used under clearance, centered fit explicit,
 all operations under `Final`; weight tags priors respected. Particularly useful:
 a projected-field message can continue at ANY valuation, need not compare sizes
 or be in a common footprint with its unprojected ancestors. Lock the cert for the
 corresponding smaller compact detector uses before continuing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}
inductive Pen (K:Final C H S)(T:Fareway I)(L:Finset ℝ) : ℝ → Fabric I → Art S I → ℝ → Prop
 | tip {P x a} (h:Contains T P x)(v:S.Tag): Pen K T L a P (fun i=>letter S (x i) v) ((v.1:ℝ)*a)
 | zero {P a w}: Pen K T L a P 0 w
 | scale {P a A w u z}(he:T.Costs (z:I→ℂ) u)(h:Pen K T L a P A w): Pen K T L a P (fun i=> z i • A i) (u+w)
 | add {P a A B u}(h:Pen K T L a P A u)(hk:Pen K T L a P B u): Pen K T L a P (A+B) u
 | cf {a P A B w}(h:Pen K T L a P A w)(he:A=ᶠ[T.via] B): Pen K T L a P B w
 | mono {a P A w u}(h:Pen K T L a P A w)(he:w≤u): Pen K T L a P A u
 | weaker {P Q a A w}(h:Pen K T L a P A w)(he:Extends T Q P): Pen K T L a Q A w
 | mul {P Q a A B w u}(h: Pen K T L a P A w)(he:Pen K T L a Q B u)(hp:Cross T P Q a): Pen K T L a (P⊔Q) (A*B) (w+u)
 | feed {P a b A w x}(h:Pen K T L a P A w)(ha:a∈L)(hb:b≤a)(hp:Local T P x a)(hx:Contains T P x):Pen K T L b P A w
 | refuse {P a b A w x}(h:Pen K T L a P A w)(ha:a∈L)(hb:b≤a)(hp:Local T P x a)(hx:Contains T P x)(d:ℕ)(hc:Forest.Centered T P x K d): Pen K T L b P (fun i=> reject K (x i) d (A i)) (w-((d:ℝ)+1)*(a-b))
 | pass {P Q a b A w x}(h:Pen K T L a P A w)(ha:a∈L)(hp: Local T P x a)(hx:Contains T Q x)(d:ℕ)(hc:Forest.Centered T P x K d): Pen K T L b Q (fun i=> part K (x i) d (A i)) (w-d*(a-b))
variable {T: Fareway I} {K:Final C H S}{L L':Finset ℝ}{P:Fabric I}{A:Art S I}{w a u b:ℝ}
namespace Pen
variable (h:Pen K T L a P A w)
include h
lemma intact : Intact T P A:=by
    induction h with
    | tip h v=> exact h.mono (fun i hi=> Acts.letter hi v)
    | zero=> exact Eventually.of_forall fun i=> Acts.zero
    | scale z he ih=> exact ih.mono (fun i hi=> hi.scale _)
    | add g h ih jh=> exact Intact.plus ih jh
    | cf h hk ih=> exact (ih.and hk).mono (fun i hi=> hi.2 ▸ hi.1)
    | mono h he ih=> exact ih
    | weaker h he ih=> exact Intact.weaker ih he
    | mul h hk he ih jh=> exact Intact.product ih jh he
    | feed h ha hb hp hx ih=> exact ih
    | refuse h ha hb hp hx d hc ih=> exact (ih.and hx).mono (fun i hi=> hi.1.sub (acts_all K d _ _ hi.2))
    | pass h ha hp hx d hc ih=> exact hx.mono (fun i hi=> acts_part K d _ _ hi)
lemma spectrum (he:L ⊆ L') : Pen K T L' a P A w:=by induction h with
   | tip h v=> exact tip h v | zero=> exact zero
   | scale v h ih=> exact ih.scale v
   | add h g ih jh=> exact ih.add jh
   | cf h he ih=> exact ih.cf he
   | mono h hk ih=> exact ih.mono hk
   | weaker h hk ih=> exact ih.weaker hk
   | mul h hk hv ih jh=> exact ih.mul jh hv
   | feed h ha hb hp hx ih=> exact ih.feed (he ha) hb hp hx
   | refuse h ha hb hp hx d hc ih=> exact ih.refuse (he ha) hb hp hx d hc
   | pass h ha hp hx d hc ih=> exact ih.pass (he ha) hp hx d hc
omit h
lemma sums {V:Type*}(s:Finset V){A:V→Art S I}(h:∀ i∈s,Pen K T L b P (A i) w): Pen K T L b P (fun i=>∑ j∈s,A j i) w:=by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact zero
   | @insert i s he ih=> simp_rw [Finset.sum_insert he]; exact (h _ (mem_insert_self ..)).add (ih fun i hi=> h _ (mem_insert_of_mem hi))
lemma suits (K: Final C H S) (d:ℕ){v:I→ S.Field d}{x:I→ E4}(he:T.Costs v u)(hx:Contains T P x): Pen K T L b P (fun i=> Tale.suit K (x i) d (v i)) (u+d*b):=by
   simp_rw [suit_eq]; apply Pen.sums (w:=u+d*b); intro i _; exact (tip hx ⟨d,(marker K d i).val⟩).scale (he.mapped (LinearMap.toContinuousLinearMap ((marker K d).coord i ∘ₗ face K d)))
end Pen
structure Credit (K: Final C H S)(T:Fareway I)(L:Finset ℝ) : Prop where
   hall : ∀ P (A:Art S I) w (s:I→StateIndex K), Pen K T L 0 P A w→ T.Costs (polled K s A) w
   head : ∀ P A w a, Pen K T L a P A w→ a∈ L→ ∀ d x, Local T P x a→ Forest.Centered T P x K d→ T.Costs (fun i=> pitch K (x i) d (A i)) (w-d*a)
end YM.Frontier6.Forest
