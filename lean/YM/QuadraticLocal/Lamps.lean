import YM.QuadraticLocal.Manifold
import YM.Next.FOUNDATIONS.Readout
/-!
Support & full norm currency for the **actual** pointwise qlocal statements. In particular
these aren't masked field VALUE sup instead of the kernel derivative norm. Stronger supplier
interface until ready to report (`LocalComparison.Taste`, which uses the factorial norm and
per-mark norms instead of the Hit on all x). We keep layouts with arbitrary test-space and
row (then countable, MAY be empty ⇒ no padding required). No changing rows to make the bound
work on each test. A row while living behind a mask always uses its stated support.

We've included flagless rows to treat FIELD-INDEPENDENT global marks, keeping their own stencils
and billing them as strongly as masked H: we leave no loophole here for an unpaid moving-mask
contribution. (One-cut captions and units can be paid with this stronger currency.) The step
factorization must preserve these as well as regular rows in `log`; see its application later.

Tests/addresses may pay by using stronger supports/widths and held arguments. Roots must
travel. We don't classify test seminorm (interface `IndependentTests`) or certify larger location/
stencil or caller locus here. It's possible to verify structural properties at EVERY unit test
while NOT having a tight enough majorant (post-block slack won't pay volume). Our `Paid` predicate
quantifies `T` inside each element purchase. Discharge this on actual history/schedule.

Radii placement remains a prerequisite for price: includes temporary shrinking against each mark
separately, not a `ω` absolute polymer extension unrooted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V : Type*} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {ι μ T T' : Type*} {w : V → ℝ} {a α β δ γ b C : ℝ} {B : ℕ}
-- Occurrences in connected H
structure Lamps (T ι : Type*) (G : Gauge)(p:BudgetPoint) (o:V→Site n)(R:Census V) where
  mode : ι→ R.Mode
  live i : mode i ≠ R.quiet
  address : ι→ RegularAddress n
  roots i (v:V) : v∈ (mode i).val → o v ∈ (address i).support
  nominal : T → ι→ Config G n → ℂ
  legal t i : p.Regular (address i).support (nominal t i)
  clear : ι→ Prop
  pure (t:T) (i:ι) (U:Config G n) : clear i → nominal t i U= nominal t i 1
namespace Lamps

variable (L:Lamps T ι G p o R)
def pullback (φ:T'→T): Lamps T' ι G p o R:= { L with
    nominal:= L.nominal ∘ φ
    legal _:= L.legal _
    pure _:= L.pure _ }
def ground (i:ι): Support n:= (L.address i).support
def light (t:T) (i:ι) (U:Config G n): ℂ:= if L.clear i then L.nominal t i U else masked p.threshold (L.ground i) (L.nominal t i) U
structure Paid (w : V→ℝ) (B:ℕ)(a C:ℝ): Prop where
  budget : ∃ f:ι→ℝ, (∀ i,0≤ f i) ∧ (∀ i t (u:Site n), u ∈ L.ground i→ p.supBounds u (L.ground i) (L.nominal t i) (f i))∧
    Hit L.ground B (fun i=> Poly.toll w (L.mode i) * f i) a C
lemma loan_monotone (h:L.Paid w B a C) (hC:C≤δ) : L.Paid w B a δ:=by obtain ⟨f,h,hf,hH⟩:=h.budget; exact ⟨f,h,hf,fun i=>budget_loosen (hH i) hC⟩
lemma light_size (i t U) (hb:p.supBounds (L.address i).site (L.ground i) (L.nominal t i) b) : ‖L.light t i U‖≤ b:=by
    have h (W): Healthy p.threshold (L.ground i) W→ ‖L.nominal t i W‖ ≤ b:= fun hi=> hb.2 W hi [] (Nat.zero_le _) (by simp)
    unfold light; split
    next hc=> rw [L.pure _ _ _ hc]; exact h 1 (one_healthy _ _ p.threshold_pos.le)
    next=> by_cases hh:Healthy p.threshold (L.ground i) U; rw [masked_eq _ _ _ _ hh]; exact h U hh
           rw [masked_ne _ _ _ _ hh,norm_zero]; exact hb.1
def frame (i:ι) (t:T) (U:Config G n): Poly R:= Poly.send (L.mode i) (L.light t i U)
def log (t:T)(U:Config G n) : Poly R:= ∑' i,L.frame i t U
open RG3.Letters
variable {L}
lemma Paid.sums (h:L.Paid w B a C) (ha:0≤a) (hw:∀ v,0<w v) (t:T)(U:Config G n): Summable (fun i=> L.frame i t U):=by
   obtain ⟨f,hf,hC,h⟩:=h.budget; apply (Poly.budgeted hw (Frame.from_hit B a C _ (fun i=> ⟨_,(L.address i).anchor⟩) (fun i=> mul_nonneg (Poly.worth hw _).le (hf i)) ha h).2.1 (fun i=>?_)).1
   rw [frame,Poly.solo]; exact mul_le_mul_of_nonneg_left (L.light_size i t U (hC i t _ (L.address i).anchor)) (Poly.worth hw _).le
@[simp] lemma frame_quiet (i t U): (L.frame i t U).part R.quiet=0:= (Poly.part_send ..).trans (if_neg (L.live i).symm)
lemma quiet_of_hasSum (t:T)(U:Config G n)(hs: Summable (fun i=>L.frame i t U)) : (L.log t U).part R.quiet=0:=by rw [log,Poly.share hs]; simp_rw [frame_quiet,tsum_zero]

variable (L) (A:Lamps T μ G p o R)

/-- Add *occurrences* (which may overlap). -/
def join : Lamps T (ι⊕μ) G p o R where
 mode := Sum.elim L.mode A.mode
 live i:= Sum.rec (motive:=fun i=> Sum.elim L.mode A.mode i ≠ R.quiet) L.live A.live i
 address := Sum.elim L.address A.address
 roots i v:= by cases i; exact L.roots _ v; exact A.roots _ v
 nominal t:= Sum.elim (L.nominal t) (A.nominal t)
 legal t i:= by cases i; exact L.legal _ _; exact A.legal _ _
 clear:= Sum.elim L.clear A.clear
 pure _ i _:= by cases i; exact L.pure _ _ _; exact A.pure _ _ _
variable {L A}
lemma joinPaid (h:L.Paid w B a C)(hh:A.Paid w B a δ): (L.join A).Paid w B a (C+δ):=by
   obtain ⟨f,hf,hP,hF⟩:=h.budget; obtain ⟨g,hg,hQ,hG⟩:= hh.budget
   let k := Sum.elim f g; refine ⟨k,?_,?_,?_⟩
   · intro i; cases i; exact hf _; exact hg _
   · intro i; cases i; exact hP _; exact hQ _
   intro x; let M (i:ι⊕μ) := if x∈(L.join A).ground i then Poly.toll w ((L.join A).mode i)*k i*Real.exp (a*coverNumber B ((L.join A).ground i)) else 0
   have h₁ : SumBudget (M ∘ Sum.inl) C := hF x; have h₂ : SumBudget (M ∘ Sum.inr) δ := hG x; have he:= h₁.2.1.hasSum.sum (f:=M) h₂.2.1.hasSum
   refine ⟨?_,he.summable,he.tsum_eq.trans_le (add_le_add h₁.2.2 h₂.2.2)⟩
   intro i; cases i; exact h₁.1 _; exact h₂.1 _
lemma joinLog (t:T)(U:Config G n) (hs:Summable (fun i=> L.frame i t U)) (hp:Summable (fun i=> A.frame i t U)): (L.join A).log t U=L.log t U+A.log t U:= by
   exact (HasSum.sum (f:=fun i=>(L.join A).frame i t U) hs.hasSum hp.hasSum).tsum_eq -- bind t U
end Lamps

section Frame
open Fusion.Attached
variable {P : ℕ → ForcedAddress G n} {X : Activities G n}
variable (K:Hard T p X.forced X.K o R)
-- K ledger summability, fixed geometry only qualitative
namespace Hard
lemma packet_summing (h: Paid K w B a C)(ha:0≤a)(hw:∀ v,0<w v)(t:T)(U:Config G n) : Summable (packet X p (K.hard t) U):=by
    obtain ⟨f,hg,hH⟩:=h.wages; let g i:= Poly.price w (f i); have hz:= (RG3.Letters.Frame.from_hit B a C g (fun i=> (X.forced i).inventory_ne.mono (X.forced i).inventory_sup) (fun i=> Poly.nonnegative hw (f i)) ha hH).2.1
    exact (Poly.budgeted hw (summable_finsetProd_of_summable_nonneg (fun i=> Poly.nonnegative hw (f i)) hz) (fun i=> by
        unfold packet; split; next=> exact (Poly.multiple hw ..).trans (Finset.prod_le_prod (fun i _=> Poly.nonnegative hw _) (fun i _=> (hg i t U).reprice _ hw))
        next=> rw [Poly.zero_price]; exact Finset.prod_nonneg fun i _=> Poly.nonnegative hw _ )).1
lemma packet_quiet (s:Finset ℕ)(U:Config G n) (t:T): (packet X p (K.hard t) U s).part R.quiet=(X.gasOccurrence p s U:ℂ):=by
    unfold packet Activities.gasOccurrence; split; next=>
       suffices he : ∀ s:Finset ℕ, (∏ i∈s,K.hard t i U).part R.quiet=↑(∏ i∈s,X.K i U) by exact he _
       intro s; induction s using Finset.induction with
       | empty => simp
       | insert i s hi ih => rw [prod_insert hi,prod_insert hi,Poly.quiet_mul,K.quiet,ih,Complex.ofReal_mul]
    next=> simp
lemma packet_of_quiet (t:T)(U:Config G n)(hs:Summable (packet X p (K.hard t) U)): (∑' i,packet X p (K.hard t) U i).part R.quiet= (X.gas p U:ℂ):=by rw [Poly.share hs]; simp_rw [packet_quiet]; exact (Complex.ofReal_tsum _).symm
end Hard

/-- Entire represented density polynomial, prior Haar, using scalar and base of EXACT
construction (up to the chosen exact representation authorized by a separate Carrier) on all links. -/
structure Gallery (T ι : Type*) (o:V→Site n) (P:Rep G n)(R:Census V) where
 E : Lamps T ι G P.p o R
 K : Hard T P.p P.activities.forced P.activities.K o R

namespace Gallery
variable {P : Rep G n} (A:Gallery T ι o P R)
-- price for exponent and actual K side
structure Pays (w:V→ℝ)(a b c : ℝ): Prop where
 budget : A.E.Paid w P.p.B a b
 wages : A.K.Paid w P.p.B a c

variable [Fintype V]

def gas (t:T)(U:Config G n): Poly R:= ∑' i, packet P.activities P.p (A.K.hard t) U i
def density (t:T)(U:Config G n): Poly R:= (Complex.ofReal (Real.exp (P.exponent U))) • (Poly.pass (A.E.log t U)* A.gas t U)
lemma same (h:A.Pays w a b δ)(ha:0≤a)(hw:∀ v,0<w v)(t:T)(U:Config G n) : (A.density t U).part R.quiet= (P.eval U:ℂ):= by
    rw [density,Poly.part_smul,Poly.quiet_mul,Poly.pass_part _ (Lamps.quiet_of_hasSum t U (h.budget.sums ha hw ..)),one_mul]; unfold gas; rw [Hard.packet_of_quiet A.K t U (Hard.packet_summing _ h.wages ha hw ..), Rep.eval, Complex.ofReal_mul]
-- for aligning on actual vacuum THROUGHOUT, no integration/division claims
end Gallery
end Frame
end YM.QuadraticLocal
