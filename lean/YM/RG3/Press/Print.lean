import YM.RG3.Press.Article

/-!
# Exact publishing of alternative marked entries

from the complete function-valued receipt. Keep breathing globals and
regular rows of the target, only replace forced partners. Preserve provenance
of each whole input entry via injective `(letter, coefficient mode)` code even
when routed to one address. Empty filler issues a fire-tag (Bands convention);
so for the marked endpoint need Nonempty marker alphabet. `Support` and
`eligible` on the route are on the ACTUAL flag geometry even for winding
pieces. No hidden pure-test terms in this publication (caller keeps units and
adds any wider quiet-free constants separately on same algebra).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Press.Article
open Lattice Wilson RG Overlay Extra.Trajectories Marker Finset Function MeasureTheory Ac Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {α : Type*} [Countable α]
variable {V : Type*} [DecidableEq V] [Nonempty V] {R : Census V} {p : BudgetPoint} {v : V → Site n}
variable (d : Article α p G R v) {P : Rep G n} (T : Bands R P) (slot : α → ℕ)

abbrev Key (α : Type*) (R : Census V) := α × {i : R.Mode // i ≠ R.quiet}

-- target second index independent of slot code.
def scored (b : ℕ) (k : Key α R) (U : Config G n) := if slot k.1=b then (d.flow k.1 U).part k.2.val else 0

def impression : Bands R P := {
  T with
    marks _ := unpin (fun k : Key α R => k.2.val) (R.fire (Classical.arbitrary V))
    entries i := unpin (d.scored slot i) 0 }

@[simp] theorem scored_pin (i : ℕ) (k : Key α R) : (d.impression T slot).entries i (pin k) = d.scored slot i k := unpin_pin ..
omit [Countable α] [Nonempty V] in
theorem scored_unfold (k : Key α R) : d.scored slot (slot k.1) k = fun U => (d.flow k.1 U).part k.2.val := by
  unfold scored; simp

lemma scored_blank (i j : ℕ) (h : j∉ Set.range (pin : Key α R → ℕ)) : (d.impression T slot).entries i j = 0 := unpin_blank _ _ h
@[simp] theorem marked_pin (i : ℕ) (k : Key α R) : (d.impression T slot).marks i (pin k) = k.2.val := by simp only [impression, unpin_pin]
lemma marked_blank (i j : ℕ) (h : j∉ Set.range (pin : Key α R → ℕ)) : (d.impression T slot).marks i j = R.fire (Classical.arbitrary V) := by simp only [impression, unpin_blank (fun k : Key α R => k.2.val) _ h]

omit [Nonempty V] in
/-- part to polynomial sum; dropping the vacuum, at a fixed coefficient
radius. Uses no bounds on argument derivatives; keep these K values even
for full next-step integral away from healthy globally. -/
lemma record_sum {a : Poly R} : (∑ i : {l : R.Mode // l ≠ R.quiet}, Poly.send i.val (a.part i.val)) = a - Poly.send R.quiet (a.part R.quiet) := by
  apply Poly.ext; intro i
  rw [Poly.part_sum,sub_eq_add_neg]; simp only [Poly.part_plus,Poly.part_neg, Poly.part_send]
  by_cases he : i = R.quiet
  · subst i
    rw [sum_eq_zero (fun x _ => if_neg (Ne.symm x.property))]; simp
  rw [if_neg he,neg_zero,add_zero,sum_eq_single (⟨_,he⟩ : {l : R.Mode // l ≠ R.quiet})]
  · simp
  · intro x _ hj; exact if_neg fun h => hj (Subtype.ext h.symm)
  simp

lemma identical (i : ℕ) (U : Config G n) {A w} (hw : ∀ j,0 < w j) (HD : d.Budget w A)
    (hQ : d.broth slot i U = (P.activities.K i U : ℂ)) :
    (d.impression T slot).each i U=d.stream slot i U := by
  let β := {c : α // slot c=i}
  let j c (s : {l : R.Mode // l ≠ R.quiet}) := Poly.send s.val ((d.flow c U).part s.val)
  let a (c : β) := d.flow c.val U
  have H := ((Poly.budgeted hw (d.flow_abs hw HD U) (fun _ => le_rfl)).1).comp_injective (i:=fun c : β => c.val) Subtype.val_injective
  have hp (s : R.Mode) : Continuous (fun x : Poly R => Poly.send s (x.part s)) := (Bands.sends s).comp (Poly.part_cont _)
  have hz (s : {l : R.Mode // l ≠ R.quiet}) :
      HasSum (fun c : β => j c.val s) (Poly.send s.val ((d.stream slot i U).part s.val)) := by
    let f : Poly R →+ Poly R := { toFun := fun x => Poly.send s.val (x.part s.val), map_zero' := by simp, map_add' := fun x y => by ext; simp only [Poly.part_plus,Poly.part_send]; split <;> simp }
    exact H.hasSum.map f (hp _)
  let e (x : {l : R.Mode // l ≠ R.quiet} × β) : ℕ := pin ((x.2.val, x.1) : Key α R)
  have he : Injective e := by
    rintro ⟨a,b⟩ ⟨a',b'⟩ hs
    have h := pin_injective hs
    -- code order reversed for tsum_prod
    exact Prod.ext (congrArg Prod.snd h) (Subtype.ext (congrArg Prod.fst h))
  let g (k) := (d.impression T slot).tagged i k U
  have hs (x : {l : R.Mode // l ≠ R.quiet} × β) : g (e x) = j x.2.val x.1 := by
    dsimp only [g,e,Bands.tagged]; rw [d.marked_pin, d.scored_pin]; change Poly.send x.1.val (if slot x.2.val=i then _ else _) = _
    rw [if_pos x.2.property]
  have hs0 : Function.support g ⊆ Set.range e := by
    rintro y hy
    by_cases h : y∈ Set.range (pin : Key α R → ℕ)
    · obtain ⟨k,rfl⟩ := h
      by_cases hki : slot k.1=i
      · exact ⟨(k.2,(⟨k.1,hki⟩:β)),rfl⟩
      exfalso; apply hy
      change Poly.send _ ((d.impression T slot).entries i (pin k) U)=0
      rw [d.scored_pin, scored, if_neg hki, Poly.send_zero]
    exfalso; apply hy
    change Poly.send _ ((d.impression T slot).entries _ y U)=_
    rw [d.scored_blank T slot _ _ h]; apply Poly.send_zero
  let f (x : {l : R.Mode // l ≠ R.quiet} × β) := j x.2.val x.1
  have hf : Summable f := by
    -- finite first type, sum of costs proof to avoid Countable etc
    obtain ⟨m,hm,hr⟩ := Poly.equivalent_norm (R:=R) hw
    have H' := (d.flow_abs hw HD U).comp_injective (i:=fun c : β => c.val) Subtype.val_injective
    apply Summable.of_norm
    apply (summable_prod_of_nonneg fun i => norm_nonneg (f i)).mpr
    refine ⟨fun i => (H'.mul_right m).of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => (hr _).trans (mul_le_mul_of_nonneg_right ?_ hm)),Summable.of_finite⟩
    change Poly.price w (Poly.send i.val ((d.flow c.val U).part i.val)) ≤ _
    rw [Poly.solo]
    exact Poly.member hw _ _
  unfold Bands.each; rw [← hQ]
  change _+(∑' k,g k)=_
  rw [← Pad.sums _ he f g hs hs0,hf.tsum_prod]
  change _ + (∑' l,∑' c : β,j c.val l) = _
  rw [tsum_fintype]
  simp_rw [(hz _).tsum_eq]
  rw [record_sum, ← d.stream_part_quiet slot hw HD]
  abel

lemma same_cluster {A w} (hw : ∀ j,0 < w j) (HO : d.Hosting P slot) (HD : d.Budget w A)
    (hQ : ∀ i U,d.broth slot i U = (P.activities.K i U : ℂ)) (U : Config G n) :
    (d.impression T slot).cluster U=d.cluster U := by
  classical
  rw [← (d.repacked P slot hw HO HD U).tsum_eq]
  unfold Bands.cluster
  refine tsum_congr fun i => ?_
  unfold Bands.packet; split
  · apply prod_congr rfl; intro i _
    exact d.identical T slot _ U hw HD (hQ i U)
  rfl

end YM.RG3.Press.Article
