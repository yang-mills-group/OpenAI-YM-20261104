import YM.RG3.Press.Print

/-!
# Publish bands with normalized costs for future steps

Powers/derivative/regular mask prices on all underlying E/H unchanged,
full forced support cost kept on both vacuum and marked. Receives *one*
price sum per site over all merged coefficients, which will reanchor to
separate marker entries without loss (including for mixed coefficients
at every one of their origins). Fixed additional root/address/held-test
budgets, if used, must be transported additionally, e.g. same bounds using
full sup over a specified family of task densities and retained address
supports; no sup/tsum interchange authorization from ordinary budgets.

Covers output with `A ≤ δ*b`, so divided forced estimates for the
represented remainder can choose nominal divisor `b` and price `δ` using
the reserve from `Shelf.Stock.bought` (any such choice is at fixed field
family). Radii published here are at every w of the input receipt. Ability
to **restore** a larger radius cannot be assumed from publishing alone (see
later ledger).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Press.Article
open Lattice Wilson RG Overlay Extra.Trajectories Marker Finset Function MeasureTheory Ac Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {α : Type*}
variable {V : Type*} [DecidableEq V] [Nonempty V] {R : Census V} {p : BudgetPoint} {v : V → Site n}
variable (d : Article α p G R v) {P : Rep G n} (T : Bands R P) (slot : α → ℕ)

section Published
variable [Countable α]

-- separate Log receipt for output H etc so can start with arbitrary E, EH
structure Contents : Prop where
  rays i : (T.rays i).val.Nonempty
  home i j : j∈ (T.rays i).val → T.origins j ∈ T.support i
  regular i : P.p.Regular (T.support i) (T.H i)

structure LogBounds (w : V → ℝ) (u c : ℝ) : Prop where
  allowance i : w i * ‖T.units i‖ ≤ u
  bulk : ∃ t : ℕ→ℝ, (∀ i,0≤t i ∧ ∀ x∈ (T.rays i).val, P.p.supBounds (T.origins x) (T.support i) (T.H i) (t i)) ∧
    ∀ i : V, SumBudget (fun j => if i∈ (T.rays j).val then Poly.toll w (T.rays j)*P.p.mass (T.support j) (t j) else 0) c

lemma impressed_active (ho : d.Hosting P slot) (hT : v = T.origins) (HT : Contents T) (hd : d.Sound) : (d.impression T slot).Active := by
  constructor
  · exact HT.rays
  · exact HT.home
  · exact HT.regular
  · intro i j; by_cases hh : j ∈ Set.range (pin : Key α R → ℕ)
    · obtain ⟨a,rfl⟩ := hh; rw [marked_pin]
      apply nonempty_iff_ne_empty.mpr; intro he
      exact a.2.property (Subtype.ext he)
    rw [d.marked_blank T slot _ _ hh]; exact singleton_nonempty _
  · intro i j; by_cases hh : j∈ Set.range (pin : Key α R → ℕ)
    · obtain ⟨k,rfl⟩ := hh
      by_cases h : slot k.1=i
      · subst i
        rw [d.scored_pin, d.marked_pin, d.scored_unfold]
        intro hn a ha
        obtain ⟨U,hU⟩ := Function.ne_iff.mp hn
        rw [← ho.equal_span]
        change T.origins a ∈ _
        rw [← hT]
        exact (hd.payload k.1).carry U k.2.val hU a ha
      rw [scored_pin]
      intro hv; exfalso; apply hv; funext U; rw [scored,if_neg h]; rfl
    rw [scored_blank _ _ _ _ _ hh]; simp
  · intro i j; by_cases h : j∈ Set.range (pin : Key α R → ℕ)
    · obtain ⟨k,rfl⟩ := h; rw [scored_pin,ho.clock]
      by_cases he : slot k.1=i
      · subst i; rw [scored_unfold,← ho.equal_span]
        exact fun U W ha hb => congrArg (fun a : Poly R => a.part k.2.val) ((hd.payload k.1).reads U W ha hb)
      intro U W _ _; dsimp [scored]; rw [if_neg he,if_neg he]
    rw [d.scored_blank _ _ _ _ h]; exact fun _ _ _ _ => rfl
  · intro i j U; by_cases h : j∈ Set.range (pin : Key α R → ℕ)
    · obtain ⟨k,rfl⟩ := h; rw [scored_pin]
      unfold scored; split
      next he =>
        subst i; intro hf
        have he' : d.flow k.1 U ≠ 0 := fun a => hf (congrArg (fun a : Poly R => a.part k.2.val) a)
        refine ⟨?_,ho.accepts k.1 U he'⟩
        rw [← ho.equal_span, ← ho.equal_inv, ho.clock]
        exact (hd.ready k.1 U he').1
      simp
    rw [d.scored_blank _ _ _ _ h]; simp
  · intro i j; by_cases h : j∈ Set.range (pin : Key α R → ℕ)
    · obtain ⟨k,rfl⟩ := h; rw [scored_pin]; by_cases h : slot k.1=i
      · subst i; rw [scored_unfold]; exact (Poly.part_cont _).measurable.comp (hd.payload k.1).borel
      unfold scored; simp only [if_neg h]; exact measurable_const
    rw [d.scored_blank _ _ _ _ h]; exact measurable_const
  intro i j k U; by_cases h : j∈ Set.range (pin : Key α R → ℕ)
  · obtain ⟨s,rfl⟩ := h; rw [scored_pin]; unfold scored; split
    · rw [(hd.payload s.1).gauge k U]
    rfl
  rw [d.scored_blank _ _ _ _ h]; rfl

-- Keep the full receipt as a function of the authorized price only
-- (`d` enters only through allows of marker origins in the stamped support),
-- so the SAME witness may be used for a whole sup family even though d.flow
-- itself varies.
def imprint (k : Key α R) : ℕ × ℕ := (slot k.1,pin k)

open scoped Classical in
def usury (v : V → Site n) (W : α → Support n) (y : α → Poly R) (s : Key α R) :=
  if ∀ j∈ s.2.val.val,v j ∈ W s.1 then ‖(y s.1).part s.2.val‖ else 0

def voucher (v : V → Site n) (W : α → Support n) (y : α → Poly R) : ℕ × ℕ → ℝ :=
  Function.extend (imprint (R:=R) slot) (usury v W y) 0

lemma chosen_profile (ho : d.Hosting P slot) (hd : d.Sound) {y w A} (hw : ∀ i,0<w i)
    (hy : ∀ i U, Width.Covered (d.flow i U) (y i)) (H : Hit d.span p.B (fun i => Poly.price w (y i)) p.supportExponent A) :
    let t := voucher slot v d.span y
    (∀ i j,0≤t (i,j) ∧ ∀ U, ‖(d.impression T slot).entries i j U‖ ≤ t (i,j)) ∧
      ∀ i : V, SumBudget (fun k => if i∈ ((d.impression T slot).marks k.1 k.2).val then
        Poly.toll w ((d.impression T slot).marks k.1 k.2)*P.p.mass (P.activities.forced k.1).support (t k) else 0) A := by
  classical
  let e (s : Key α R) := (slot s.1,pin s)
  have he : Injective e := fun _ _ h => pin_injective (congrArg Prod.snd h)
  let u (s : Key α R) := if ∀ j∈ s.2.val.val,v j ∈ d.span s.1 then ‖(y s.1).part s.2.val‖ else 0
  have hu (s : Key α R) : 0≤u s := by unfold u; split <;> positivity
  let t := Function.extend e u 0
  have ht (i) : t (e i)=u i := he.extend_apply ..
  have ht' (j) (h : j∉Set.range e) : t j=0 := Function.extend_apply' u (0:ℕ×ℕ→ℝ) j h
  intro T'
  have hh' : T'=t := by
    -- Classical choice of membership may differ; same condition
    dsimp only [T',t,voucher,imprint,e,usury,u]; congr
  rw [hh']
  refine ⟨fun i j => ?_,fun i => ?_⟩
  · by_cases hi : (i,j) ∈ Set.range e
    · obtain ⟨k,hk⟩ := hi
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hk
      rw [scored_pin,scored_unfold,ht k]
      refine ⟨hu _,fun U => ?_⟩
      unfold u; split
      · exact (hy k.1 U k.2.val).1.trans_eq ((hy k.1 U).norm _).symm
      next h =>
        change ‖(d.flow k.1 U).part k.2.val‖ ≤ 0
        rw [show (d.flow k.1 U).part k.2.val=0 from by_contra fun hh => h ((hd.payload k.1).carry U _ hh),norm_zero]
    have hz : (d.impression T slot).entries i j=0 := by
      by_cases hj : j∈Set.range (pin : Key α R → ℕ)
      · obtain ⟨s,rfl⟩ := hj
        rw [d.scored_pin T slot i]
        funext x; rw [scored,if_neg (show slot s.1≠i from fun h => hi ⟨_,Prod.ext h rfl⟩)]; rfl
      exact d.scored_blank T slot i _ hj
    rw [hz,ht' _ hi]; simp
  let q (s : Key α R) := if i∈s.2.val.val then
    Poly.toll w s.2.val*p.mass (d.span s.1) (u s) else 0
  have hN (s) : 0≤q s := by
    unfold q; split <;> first | exact le_rfl | exact mul_nonneg (Poly.worth hw _).le (BudgetPoint.loMass p _ _ (hu _ ) |>.trans' (hu _))
  have hq (a : α) : ∑ l : {l : R.Mode // l ≠ R.quiet}, q (a,l) ≤
      if v i ∈ d.span a then Poly.price w (y a)*Real.exp (p.supportExponent*coverNumber p.B (d.span a)) else 0 := by
    let E := Real.exp (p.supportExponent*coverNumber p.B (d.span a))
    have hE : 0 ≤ E := (Real.exp_pos _).le
    by_cases he' : v i∈d.span a
    · rw [if_pos he',Poly.price, sum_mul]
      let t' (l : R.Mode) := Poly.toll w l * ‖(y a).part l‖ * E
      have ht l : 0 ≤ t' l := mul_nonneg (mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) hE
      calc
        _ ≤ ∑ l ∈ (univ : Finset {l : R.Mode // l ≠ R.quiet}).image Subtype.val,t' l := by
          rw [sum_image Subtype.val_injective.injOn]
          refine sum_le_sum (fun s _ => ?_)
          unfold q u BudgetPoint.mass
          dsimp only
          split_ifs <;> first | exact (show 0 ≤ t' s.val from ht _) | simpa only [mul_zero] using ht s.val | (unfold t' E; linarith)
        _ ≤ ∑ l : R.Mode,t' l := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun l _ _ => ht _
    rw [if_neg he']
    exact le_of_eq (sum_eq_zero fun s _ => by
      unfold q u; dsimp only; split_ifs with Hh Hh'
      · exact (he' (Hh' _ Hh)).elim
      all_goals simp [BudgetPoint.mass])
  have hc : SumBudget q A := by
    refine budget_fiberwise Prod.fst hN (fun a s hx => (le_trans ?_ (hq a))) (H (v i))
    calc
      _ = ∑ j ∈ s.image Prod.snd, q (a,j) := by
        rw [sum_image]
        · refine sum_congr rfl (fun j hj => congrArg q (Prod.ext (hx j hj) rfl))
        intro z hz y hy h'; exact Prod.ext ((hx z hz).trans (hx y hy).symm) h'
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ => hN _
  refine Pad.absolute e he (u:=q) (fun s => ?_) ?_ hc
  · rw [ht s]
    simp only [e,d.marked_pin, ← ho.equal_span, ho.clock,q]
  intro s hs; by_contra! hhs; apply hs
  dsimp only; rw [ht' _ hhs]
  unfold BudgetPoint.mass; split <;> simp
lemma rooted_profile (ho : d.Hosting P slot) (hd : d.Sound) {w A} (hw : ∀ i,0<w i) (HD : d.Budget w A) :
    ∃ t : ℕ × ℕ → ℝ, (∀ i j,0≤t (i,j) ∧ ∀ U, ‖(d.impression T slot).entries i j U‖ ≤ t (i,j)) ∧
      ∀ i : V, SumBudget (fun k => if i∈ ((d.impression T slot).marks k.1 k.2).val then
        Poly.toll w ((d.impression T slot).marks k.1 k.2)*P.p.mass (P.activities.forced k.1).support (t k) else 0) A := by
  obtain ⟨y,hy,h⟩ := HD
  exact ⟨voucher slot v d.span y, d.chosen_profile T slot ho hd hw hy h⟩
/-- `bands.Active` for arbitrary regular contents and divided marked hit
transport with no tag-cardinality cost. Paying the divisor using a strong
forced-only factor is before this theorem. Require not just equality of
ambient polynomial as an input; purchase on each letter, even alternatives
on common address, is indispensable. -/
theorem publish (h : d.Hosting P slot) (ht : v = T.origins) (HD : d.Sound)
    (HL : Contents T) {w u c δ b A} (hT : LogBounds T w u c)
    (hw : ∀ i,0<w i) (HA : d.Budget w A) (hb : 0<b) (hfit : A ≤ δ*b)
    (hQ : ∀ i U,d.broth slot i U = (P.activities.K i U : ℂ)) :
    let o := d.impression T slot; o.Active ∧ o.Radial w u c δ b ∧ o.cluster = d.cluster := by
  refine ⟨d.impressed_active T slot h ht HL HD,
    ⟨hw,hT.allowance,hb,hT.bulk,?_⟩,funext (d.same_cluster T slot hw h HA hQ)⟩
  obtain ⟨t,ht,H⟩ := d.rooted_profile T slot h HD hw HA
  exact ⟨_,ht,fun i => budget_loosen (H i) hfit⟩
end Published

end YM.RG3.Press.Article
