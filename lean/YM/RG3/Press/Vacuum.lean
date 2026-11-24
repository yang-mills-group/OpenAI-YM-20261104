import YM.RG3.Press.Voucher

/-!
# Printing also the vacuum, with symmetry receipt for validity

Unlike Pads.legitimate, room for ALL **new** alphabet and their full
tests, determined as part of this encoding precisely. Slots off-range can
be kept with invariant support-inventory (`K = 0`) including on a torus of
side one. Choose a target Rep for the reset path/regular/basic data first
(later consumers must ALIGN this, not assume all Reps meet the output
exponent). That permits use also for purely unmarked path changes retaining
P's beta and e.g. extraction/scalar receipts. Needs unused exponent before
merging. Exact KBound contrast by hit even on winding labels. No theorem
that changing unmarked representation here commutes with `Transfer` in
both directions; only use equality of evaluations with the same unmarked
params or emit separate push comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Press.Article
open Lattice Wilson RG Overlay Extra.Trajectories Marker Finset Function MeasureTheory Ac Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {α : Type*} [Countable α]
variable {V : Type*} [DecidableEq V] {R : Census V} {p : BudgetPoint} {v : V → Site n}
variable (d : Article α p G R v) (P : Rep G n)

structure Spin (s : Signed) (b : Site n) where
  sw : Equiv.Perm α
  span (c : α) : d.span (sw c) = (d.span c).image (affine s b)
  invoice (c : α) : d.inv (sw c) = (d.inv c).image (affine s b)
  reads c U : (d.address (sw c)).extraTest U ↔ (d.address c).extraTest (pull s b U)
  quiet c U : ((d.flow (sw c) U).part R.quiet) = ((d.flow c (pull s b U)).part R.quiet)

private def buffer : ForcedAddress G n := ⟨univ,univ,by exact univ_nonempty,subset_refl _,fun _ => True⟩

def ledger : Rep G n := {
  P with activities := { P.activities with
    forced := unpin d.address buffer
    K := unpin (fun c U => ((d.flow c U).part R.quiet).re) 0 } }

@[simp] theorem currency (c) : (d.ledger P).activities.forced (pin c) = d.address c := by simp only [ledger,unpin_pin]
@[simp] theorem fixed (c) (U) : (d.ledger P).activities.K (pin c) U = ((d.flow c U).part R.quiet).re := by simp only [ledger, unpin_pin]

theorem blankK (i : ℕ) (h : i∉ Set.range (pin (α:=α))) : (d.ledger P).activities.K i = 0 := by
  simp only [ledger,unpin_blank _ (0 : Config G n → ℝ) h]
private theorem blankA (i : ℕ) (h : i∉ Set.range (pin (α:=α))) : (d.ledger P).activities.forced i = buffer := by
  simp only [ledger,unpin_blank _ _ h]

lemma ledger_q (hd : d.Sound) (i U) : d.broth pin i U = ((d.ledger P).activities.K i U:ℂ) := by
  by_cases H : i∈ Set.range (pin (α:=α))
  · obtain ⟨a,rfl⟩ := H
    let s : {c // pin c=pin a} := ⟨a,rfl⟩
    rw [broth,tsum_eq_single s,fixed]
    · exact Complex.ext rfl (hd.honest _ U)
    intro c hc; exact (hc (Subtype.ext (pin_injective c.property))).elim
  rw [d.blankK P _ H, Pi.zero_apply, Complex.ofReal_zero]
  unfold broth
  refine (tsum_congr (g:=fun _ => 0) (fun c => (H ⟨c.val, c.property⟩).elim)).trans tsum_zero

lemma ledger_host (hp : P.p=p) (hd : d.Sound) : d.Hosting (d.ledger P) pin where
  clock := hp
  equal_span i := by rw [d.currency]
  equal_inv i := by rw [d.currency]
  accepts i U h := by rw [d.currency]; exact (hd.ready i U h).2

lemma loyal (hp : P.p=p) (hd : d.Sound) : (d.ledger P).activities.ForcedFamily (d.ledger P).p := by
  constructor <;> intro i
  all_goals
    by_cases hi : i∈ Set.range (pin (α:=α))
  all_goals
    try (change ∃ c : α,pin c=i at hi; obtain ⟨j,rfl⟩ := hi)
  · intro t U; rw [fixed,fixed,(hd.payload j).gauge t U]
  · rw [blankK _ _ _ hi]; exact fun _ _ => rfl
  · rw [currency]; exact hd.invariantTest j
  · simp_rw [blankA _ _ _ hi]; exact fun _ _ => Iff.rfl
  · have he := Complex.continuous_re.measurable.comp ((Poly.part_cont R.quiet).measurable.comp (hd.payload j).borel)
    rw [funext (fixed d P j)]; exact he
  · rw [blankK _ _ _ hi]; exact measurable_const
  · rw [currency]; exact hd.query j
  · rw [blankA _ _ _ hi]; exact MeasurableSet.univ
  · rw [currency, show (d.ledger P).p=p from hp]
    intro U W ha hf; rw [fixed,fixed,(hd.payload j).reads U W ha hf]
  · rw [blankK _ _ _ hi]; exact fun _ _ _ _ => rfl
  · rw [currency, show (d.ledger P).p=p from hp]; exact hd.reads j
  · rw [blankA _ _ _ hi]; exact fun _ _ _ _ => rfl
  · intro U; rw [fixed,d.currency, show (d.ledger P).p=p from hp]; exact fun h => hd.ready j U fun he => h (by rw [he]; rfl)
  · rw [blankK _ _ _ hi]; simp

lemma allot (hp : P.p=p) {w A} (hw : ∀ i,0<w i) (ha : d.Budget w A) : (d.ledger P).activities.KBound (d.ledger P).p A := by
  classical
  obtain ⟨y,hy,h⟩ := ha
  let a := unpin (fun c => ‖(y c).part R.quiet‖) (0:ℝ)
  have he i : a (pin i)=‖(y i).part R.quiet‖ := unpin_pin ..
  have hf i (h : i∉ Set.range (pin (α:=α))) : a i=0 := unpin_blank _ _ h
  refine ⟨a,fun i => ?_,fun x => Pad.absolute _ (pin_injective (α:=α)) (u:=fun i => if x∈d.span i then p.mass (d.span i) (‖(y i).part R.quiet‖) else 0)
    (fun i => ?_) ?_ (budget_mono (h x) ?_ ?_)⟩
  · by_cases hi : i∈ Set.range (pin (α:=α))
    · obtain ⟨i,rfl⟩ := hi; rw [he]; refine ⟨norm_nonneg _,fun U => ?_⟩
      rw [fixed]; exact (Complex.abs_re_le_norm _).trans ((hy i U _).1.trans_eq ((hy i U).norm _).symm)
    rw [d.blankK _ _ hi,hf _ hi]; simp
  · rw [he,d.currency,show (d.ledger P).p=p from hp]
  · intro i hi; by_contra h; apply hi; dsimp only; rw [hf _ h]; split
    · unfold BudgetPoint.mass; simp
    rfl
  · intro i; split
    · exact (norm_nonneg _).trans (p.loMass _ _ (norm_nonneg _))
    exact le_rfl
  intro i; split
  next hu =>
    rw [mul_comm,BudgetPoint.mass]
    have hm := Poly.member hw R.quiet (y i)
    simp only [Poly.quiet_toll,one_mul] at hm
    exact mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
  exact le_rfl

-- permute the pinned subset of natural labels exactly. Identity on its
-- complement; suitable when uniform padding is translation-invariant.
open scoped Classical in
private def pFunc (f : Equiv.Perm α) (i : ℕ) : ℕ := if h : i∈ Set.range (pin (α:=α)) then pin (f h.choose) else i
private theorem p_map (f : Equiv.Perm α) (c : α) : pFunc f (pin c)=pin (f c) := by
  unfold pFunc; rw [dif_pos (Set.mem_range_self _)]; congr 2
  apply pin_injective
  exact (show pin (Set.mem_range_self (f:=pin) c).choose = pin c from (Set.mem_range_self ..).choose_spec)
private def perm (f : Equiv.Perm α) : Equiv.Perm ℕ where
  toFun := pFunc f
  invFun := pFunc f.symm
  left_inv i := by by_cases hi : i∈ Set.range (pin (α:=α)); obtain ⟨c,rfl⟩ := hi; rw [p_map,p_map,Equiv.symm_apply_apply]; unfold pFunc; rw [dif_neg hi,dif_neg hi]
  right_inv i := by by_cases hi : i∈ Set.range (pin (α:=α)); obtain ⟨c,rfl⟩ := hi; rw [p_map,p_map, Equiv.apply_symm_apply]; unfold pFunc; rw [dif_neg hi,dif_neg hi]

lemma refunds (s : Signed) (b : Site n) (S : d.Spin s b) (m : P.activities.Moves s b) : Nonempty ((d.ledger P).activities.Moves s b) := by
  classical
  have HK i : perm S.sw (pin i)=pin (S.sw i) := p_map _ _
  have HK' i (he : i∉Set.range (pin (α:=α))) : perm S.sw i=i := dif_neg he
  have HE : (univ : Finset (Site n)) = univ.image (affine s b) := by
    have hi : Injective (affine s b) := fun _ _ h => s.act_injective (add_right_cancel h)
    ext x; simp only [mem_univ, mem_image, true_and, true_iff]
    exact Finite.injective_iff_surjective.mp hi x
  refine ⟨⟨m.ep,perm S.sw,m.reg_site,m.reg_support,?_,?_,?_,m.valuesE,?_⟩⟩ <;> intro i
  all_goals
    by_cases hi : i∈ Set.range (pin (α:=α))
    · obtain ⟨i,rfl⟩ := hi
      simp only [HK]
      first
      | rw [currency, currency]
        first | exact S.span i | exact S.invoice i | exact S.reads i
      | intro U; rw [fixed, fixed, S.quiet]
    rw [HK' _ hi]
    first | rw [blankA _ _ _ hi]; first | exact HE | exact fun _ => Iff.rfl
          | rw [blankK _ _ _ hi]; exact fun _ => rfl

lemma lawful (hp : P.p=p) (hd : d.Sound) {σ C Λ δ W w A}
    (hw : ∀ i,0<w i) (HA : d.Budget w A) (hv : A ≤ W)
    (hpath : P.path.Bounds P.clip σ C Λ) (hE : P.activities.RegularFamily P.p) (hb : P.activities.EBound P.p δ)
    (hm : ∀ s b, Nonempty (P.activities.Moves s b)) (hspin : ∀ s b,Nonempty (d.Spin s b)) : (d.ledger P).Lawful σ C Λ δ W := by
  obtain ⟨a,ha,hA⟩ := d.allot P hp hw HA
  exact ⟨hpath, ⟨⟨hE.smooth,hE.at_flat,hE.vanish⟩,d.loyal P hp hd, fun s b =>
    d.refunds P _ _ (Classical.choice (hspin s b)) (Classical.choice (hm s b)),hb,⟨a,ha,fun x => budget_loosen (hA x) hv⟩⟩⟩

end YM.RG3.Press.Article
