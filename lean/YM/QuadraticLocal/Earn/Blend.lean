import YM.QuadraticLocal.Earn.Invoice
import YM.QuadraticLocal.Earn.Solo
import YM.QuadraticLocal.Earn.Aegis
/-!
 # Here is the purchased multi-mark output, the *actual formal render*

Reuse both receipts at once on all heights. Version bound at next step will refer
 to this namespace's assembly, not only a recomputed x(t) sheet. Analytic ABI applies
 after confirming EACH `Press` ticket is bound to the intended Wilson prescription;
 this proof doesn't assume the existence for that binding. Close recursion reuses
 these same receipts. Supports as in Rendering; footprint rebase applies to Global
 passthrough literal terms (all of them). Negatives/emission extra in functional
 comparison still costed as stated.

 The clock widths must now reserve ahead at every authority for this literal
 exponential cost. This lemma is uniform across all admitted debts, fields, periods, etc
 at the GIVEN port. Port needs to be purchased separately. Needs direct reader witness for
 f equality on REAL, Type before α and imaginary bookkeeping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice Laurent RG Wilson Marker Ac
open Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Echo AllOrder AllOrder.Ink
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e σ ρ r b :ℝ} {k i' j u i h : ℕ}
namespace Scene
set_option quotPrecheck false
open Width Club Promote Press Accumulate Cable
variable (X:ι→ Row P R G α)(q:Ratio c n)
variable (w:V→ℝ)(t:V→ℕ)
-- Ledger includes occurrence-card *and* total weighted toll if wanted. s can cover ANY extra internal rank requests, not tied to E analytical
structure Ministry (R:Census V) (t:V→ℕ) (Ψ Υ:ℕ):Prop where
   -- count separately, since cost t can include some fundamental 0 (passive or attached frames), must still meet wallet and publication gates
   quota : ∀ p:R.Mode, (p.val).card ≤ Ψ
   crew : ∀ p:R.Mode, (∑ i∈p.val,t i) ≤ Υ
structure Armada (σ:ℝ)(v:ℝ)(j k Φ:ℕ):Prop extends Ministry R t k Φ where
   positive : ∀ i,0<w i
   suggests : Offers X w σ v
   purchases : Issues X σ j t
   honor i: (X i).Budget
namespace Armada
variable (L:Armada X w t σ b j k u)
lemma degreeR (m:Ministry R t k u)(A:Row P R G α)(h:A.Credentials j t): A.lamp.e ≤ j ∧ A.lamp.toll ≤ u ∧ A.lamp.r ≤ j+u+1:=by
    have hh: A.lamp.toll ≤ u:= h.2 ▸ m.crew A.mode; exact ⟨h.1,hh, A.lamp.crest.trans (Nat.add_le_add_right (Nat.add_le_add h.1 hh) _)⟩
-- direct energy price.ALL Field.Epoch at credential
variable {U θ:ℝ} (B:BudgetPoint)(hU: Invoice.Supports B U a g σ θ)
local notation "T"=> (Invoice.price B U (j+u+1) k a θ G)
local notation "Π"=> rendered X B g
include L hU
lemma tally (m:ℕ)(x:Site n): SumBudget (fun i=>if m≤ (X i).length then (if x∈(X i).ground B then Invoice.income B X w g i*Real.exp (a*coverNumber B.B ((X i).ground B)) else 0) else 0) (Invoice.price B U (j+u+1) k a θ G * b * Real.exp (-θ)^m):= Invoice.paying B U X w L.positive _ k hU L.suggests L.purchases.spend (fun i=>(Armada.degreeR t L.toMinistry (X i) (L.purchases.usable i)).2.2) (fun i=> L.quota _) m x -- #check order
lemma hits: Hit (fun i=> (X i).ground B) B.B (Invoice.income B X w g) a (T*b):=fun x=> by simpa only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] using tally X w t L B hU 0 x
lemma paid : (Π).Paid w B.B a (T*b) := by refine ⟨ (fun i=>(X i).charge B g),?_, fun i x y hy=> (X i).supported B (g:=g) x y (L.honor i) hy, hits X w t L B hU⟩; intro i; exact mul_nonneg (mul_nonneg (by positivity) ((X i).real_quote B g).1) (X i).sound.le
omit hU L
end Armada

section result
local notation "R₀"=> Solo.Watching X
variable (S:Press X j)(B: Press.Receipt X S a e)
variable (L:Armada X w t σ b j k u)
variable (he:0≤e)(hb:b≤1)(hv:Width.Memento k q.count σ ρ a)
local notation "p₀"=> Press.Runway X q S
abbrev Texts := Solo.Watching X ⊕ Press.Runway X q S

def letters (ρ:ℝ)(i:Texts X q S): Row (P.coarser q) R G α := i.elim (Solo.capsules q X) (Press.placement X q S B ρ)

noncomputable def productivity (L':Side)(a ρ e:ℝ)(k j:ℕ):= Solo.clearBudget L' k ρ+ Width.mint L' k j a ρ *e
local notation "b₀"=> (Scene.productivity q.count a ρ e k j * b)
local notation "X₀"=> (letters X q S B ρ)
lemma join_offer {μ:Type}{X:ι→Row P R G α}{Y:μ→ Row P R G α} {g h:ℝ} (hz:Offers X w σ g)(he:Offers Y w σ h) : Offers (Sum.elim X Y) w σ (g+h):=by
    intro i; let f(T: Row P R G α) := if T.center=i then Poly.toll w T.mode * T.height σ else 0; let U (i:ι⊕μ):=f (i.elim X Y); have h₁: SumBudget (U∘Sum.inl) g:= hz i; have h₂: SumBudget (U ∘ Sum.inr) h:=he i
    have ht := h₁.2.1.hasSum.sum (f:=U) h₂.2.1.hasSum; refine ⟨fun i=>?_, ht.summable, ht.tsum_eq.trans_le (add_le_add h₁.2.2 h₂.2.2)⟩; cases i; exact h₁.1 _; exact h₂.1 _
include B he hb L hv
lemma lit : Armada X₀ w t ρ (Scene.productivity q.count a ρ e k j * b) j k u:=by
    refine ⟨L.toMinistry,L.positive,?_,⟨?_,?_⟩,?_⟩
    · unfold Scene.productivity; rw [add_mul]; exact join_offer w (Solo.offers q hv X w L.positive L.suggests (fun i=>L.quota _)) (Width.crew X q S B w L.positive (fun i=>L.quota _) hv L.suggests hb he)
    · rintro (i|i); exact Solo.retained (X i.val) q i.prop (L.purchases.spend _); exact Press.assured X i.fst q S B i.snd ρ
    · rintro (i|i); exact L.purchases.usable _; exact Press.licensed X i.fst q S B i.snd ρ t L.purchases.usable
    rintro (i|i); exact L.honor i.val; exact Press.plotted X i.fst q S B i.snd ρ L.honor
-- Revenue and long bills on subset also
variable {T H:ℕ} (M: Width.Viewer X S a T)
def hire (ρ:ℝ) (i: Width.Shaded X q S M H):= Press.placement X q S B ρ i.val
include M
lemma lost : Armada (Press.placement X q S B ρ ∘ (Subtype.val:Width.Shaded X q S M H→Press.Runway X q S)) w t ρ (Width.mint q.count k j a ρ*Width.flat a σ e T H*b) j k u:=by
    let h:= lit X q w t S B L he hb hv; exact ⟨L.toMinistry,h.positive,Width.nights X q S B w L.positive (fun i=>L.quota _) hv H M L.suggests hb he,⟨fun i=>h.purchases.spend (Sum.inr i.val),fun i=>h.purchases.usable (Sum.inr i.val)⟩,fun i=>h.honor (Sum.inr i.val)⟩
omit M L he hb hv
lemma crewC [Countable ι]: Countable (Scene.Texts X q S):=by haveI:= Press.places X q S B; unfold Scene.Texts; infer_instance
end result
end Scene
end YM.QuadraticLocal.Earn
