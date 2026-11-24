import YM.Integration.ActualRunPhysicalPages
import YM.Integration.UnmaskedPartnerAlgebra
import YM.Integration.NativeForcedPolynomialReentry
import YM.MergeProof.Bungalow

/-!
The unmasked source is split before the gas merger.  Its original pre-mask
regular kernel is retained; only the complementary leak enters the Deck.
Every old forced vertex is excluded from a dry Paper by the native `dry`
predicate, and remains in the complete forced merger.  No old K is set to zero.

The global price below is the actual section price, with its inverse-threshold
power exposed.  It is not a small forest or a restored-radius estimate.
This file is staged proof work and has not yet been compiler validated.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunUnmaskedPartners
open Finset Function MeasureTheory Lattice Wilson RG Source Marker Extra.Multi
open FVA1 PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums
open scoped BigOperators Classical

section ActualKernel
variable {G : Gauge} (R : Run G) (N p L d : ℕ)

/-- A true global value price, independent of the period and the origin once
the actual threshold and label are fixed.  The inverse threshold is not erased. -/
def globalPrice (v : R.family.label d) : ℝ :=
  BasisCost.price (R.family.localSection d) *
    ((min (R.family.path.rep N p L).p.threshold 1)⁻¹) ^
      BasisCost.slots (R.family.labels.level d) *
    (R.family.labels.level d).coeffSize v

theorem kernel_global (v : R.family.label d)
    (o : Site (R.family.side L p)) (U : Config G (R.family.side L p)) :
    ‖ActualRunPhysicalPages.kernel R N p L d v o U‖ ≤
      globalPrice R N p L d v := by
  let P := (R.family.path.rep N p L).p
  have hg : 0 < min P.threshold 1 := lt_min P.threshold_pos zero_lt_one
  simpa only [ActualRunPhysicalPages.kernel, Push.Local.presented,
    globalPrice, LinearMap.coe_mk, AddHom.coe_mk] using
    BasisCost.full_scaled (R.family.localSection d) v o hg
      (min_le_left P.threshold 1) (min_le_right P.threshold 1) U

end ActualKernel

section Leak
variable {G : Gauge} {n : Side}

def leak (t : ℝ) (s : Support n) (f : Config G n → ℂ)
    (U : Config G n) : ℂ := f U - masked t s f U

theorem split_kernel (t : ℝ) (s : Support n) (f : Config G n → ℂ)
    (U : Config G n) : f U = masked t s f U + leak t s f U := by
  unfold leak
  ring

theorem leak_healthy (t : ℝ) (s : Support n) (f : Config G n → ℂ)
    (U : Config G n) (h : Healthy t s U) : leak t s f U = 0 := by
  rw [leak, masked_eq t s f U h, sub_self]

/-- The complementary term pays the original global price, not twice it. -/
theorem leak_price (t : ℝ) (s : Support n) (f : Config G n → ℂ)
    {c : ℝ} (hc : 0 ≤ c) (hf : ∀ U, ‖f U‖ ≤ c) (U : Config G n) :
    ‖leak t s f U‖ ≤ c := by
  by_cases h : Healthy t s U
  · rw [leak_healthy t s f U h, norm_zero]
    exact hc
  rw [leak, masked_ne t s f U h, sub_zero]
  exact hf U

theorem actual_leak_price (R : Run G) (N p L d : ℕ)
    (v : R.family.label d) (o : Site (R.family.side L p))
    (s : Support (R.family.side L p))
    (U : Config G (R.family.side L p)) :
    ‖leak (R.family.path.rep N p L).p.threshold s
      (ActualRunPhysicalPages.kernel R N p L d v o) U‖ ≤
      globalPrice R N p L d v := by
  apply leak_price
  · exact (norm_nonneg _).trans (kernel_global R N p L d v o U)
  exact kernel_global R N p L d v o

/-- Only the native regular germ supplies this attachment; the mask is never
differentiated.  The flag equality is used solely for the off-chart value. -/
theorem leak_attaches (P : BudgetPoint) (s : Support n)
    (f : Config G n → ℂ) (hf : P.Regular s f) :
    Push.Local.Attaches P.threshold s (leak P.threshold s f) := by
  refine ⟨?_, ?_, hf.borel.sub (masked_measurable _ _ _ hf.borel),
    leak_healthy P.threshold s f⟩
  · intro U W hsites hflags
    have he := hf.sites U W hsites
    have hh : Healthy P.threshold s U ↔ Healthy P.threshold s W := by
      unfold Healthy
      rw [disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty, hflags]
    simp only [leak, masked, Set.indicator, Set.mem_setOf_eq, hh, he]
    rfl
  intro g U
  simp only [leak, masked, Set.indicator, Set.mem_setOf_eq, Healthy,
    gauge_flags, hf.symmetry g U]
  split_ifs <;> rfl

end Leak

section RetainedRun
variable {G : Gauge} (R : Run G) (N p L : ℕ)
    {V : Type} [DecidableEq V] [Fintype V]
    (o : Positions V (R.family.side L p)) (d : V → ℕ)
    (v : ∀ i, R.family.label (d i))

def actualLeak (i : V) : Config G (R.family.side L p) → ℂ :=
  leak (R.family.path.rep N p L).p.threshold
    (ActualRunPhysicalPages.cover R p L (d i) o i)
    (ActualRunPhysicalPages.kernel R N p L (d i) (v i) (o.origin i))

/-- Arity zero retains one copy of each independent original mark.  The forced
input is the complete barcode sum of the original, possibly infinite Nat K. -/
def actualInput : NativeCaptionDeck.Input 0 V V G (R.family.side L p) where
  roots i := o.origin i.1
  region i := ActualRunPhysicalPages.cover R p L (d i) o i
  regular i U := Poly.send ((Aged 0 V).fire (i, 0))
    (actualLeak R N p L o d v i U)
  forced s U := bar (R.family.path.rep N p L).activities (Aged 0 V) U s

theorem actual_leak_attaches (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L) (i : V) :
    Push.Local.Attaches (R.family.path.rep N p L).p.threshold
      (ActualRunPhysicalPages.cover R p L (d i) o i)
      (actualLeak R N p L o d v i) := by
  have _originalMarkerDecision : DecidableEq V := inferInstance
  have _originalMarkerFinite : Fintype V := inferInstance
  apply leak_attaches
  exact Next.Foundations.regular_larger
    (ActualRunPhysicalPages.priced R N p L (d i) hLN (href i)
      (v i) (o.origin i)).1 Finset.subset_union_left

theorem actual_input_admitted (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L) :
    (actualInput R N p L o d v).Admitted
      (R.family.path.rep N p L).p.threshold := by
  refine ⟨fun i => ?_, fun i U => ?_, fun s => ?_⟩
  · have hi := actual_leak_attaches R N p L o d v hLN href i
    refine ⟨fun U W hs hf => congrArg (Poly.send ((Aged 0 V).fire (i, 0)))
      (hi.sites U W hs hf), fun g U =>
      congrArg (Poly.send ((Aged 0 V).fire (i, 0))) (hi.symmetry g U),
      fun q => ?_, fun U => ?_⟩
    · change Measurable (fun U =>
        (Poly.send ((Aged 0 V).fire (i, 0))
          (actualLeak R N p L o d v i U)).part q)
      simp_rw [Poly.part_send]
      split
      · exact hi.borel
      exact measurable_const
    apply Push.GridApprox.Nil.scope_send
    intro j hj
    have he : j = (i, 0) := Finset.mem_singleton.mp hj
    subst j
    exact Finset.subset_union_right (o.mem i)
  · exact (Poly.part_send ..).trans
      (if_neg (Ne.symm ((Aged 0 V).fire_hot (i, 0))))
  exact Accent.granular (R.family.path.rep N p L).activities
    (R.family.path.rep N p L).p (Aged 0 V)
    (R.makes.wilson.represents N p L hLN).good.labels s

theorem actual_input_healthy_zero (i : V) (U : Config G (R.family.side L p))
    (h : Healthy (R.family.path.rep N p L).p.threshold
      ((actualInput R N p L o d v).region i) U) :
    (actualInput R N p L o d v).regular i U = 0 := by
  change Healthy (R.family.path.rep N p L).p.threshold
    (ActualRunPhysicalPages.cover R p L (d i) o i) U at h
  change Poly.send _ (leak _ _ _ U) = 0
  rw [leak_healthy _ _ _ U h, Poly.send_zero]

/-- This is an application to the actual retained input, not a record assuming
the desired full-gas equality.  Every old Nat correction enters its bar. -/
theorem actual_leak_regroup (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L)
    (U : Config G (R.family.side L p)) :
    reap (Poly.pass (∑ i, (actualInput R N p L o d v).regular i U) *
      field (fun s => bar (R.family.path.rep N p L).activities (Aged 0 V) U s)
        (flags (R.family.path.rep N p L).p.threshold U)) =
    field (fun s => (actualInput R N p L o d v).forcedOutput
      (R.family.path.rep N p L).p.threshold s U)
      (flags (R.family.path.rep N p L).p.threshold U) := by
  exact leak_full_regroup (actualInput R N p L o d v) _
    (actual_input_admitted R N p L o d v hLN href)
    (actual_input_healthy_zero R N p L o d v) U

/-- The arity-zero projection has been discharged as an actual ring map. -/
theorem actual_leak_field (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L)
    (U : Config G (R.family.side L p)) :
    field (fun s => (actualInput R N p L o d v).forcedOutput
      (R.family.path.rep N p L).p.threshold s U)
      (flags (R.family.path.rep N p L).p.threshold U) =
    Poly.pass (Mach (Bud V) (fun i => actualLeak R N p L o d v i U)) *
      Poly.bead (Bud V) ((R.family.path.rep N p L).activities.gas
        (R.family.path.rep N p L).p U : ℂ) := by
  have h := actual_leak_regroup R N p L o d v hLN href U
  have hb := Accent.hawk (R.family.path.rep N p L).activities
    (R.family.path.rep N p L).p (Aged 0 V)
    (R.makes.wilson.represents N p L hLN).good.labels U
  change field (fun s => bar (R.family.path.rep N p L).activities
    (Aged 0 V) U s) _ = _ at hb
  have hl : reap (∑ i, (actualInput R N p L o d v).regular i U) =
      Mach (Bud V) (fun i => actualLeak R N p L o d v i U) :=
    zero_reap_singletons _
  rw [hb, zero_reap_mul, zero_reap_pass, hl, zero_reap_bead] at h
  exact h.symm

def actualLog (U : Config G (R.family.side L p)) : Poly (Bud V) :=
  Mach (Bud V) (fun i =>
    ActualRunPhysicalPages.kernel R N p L (d i) (v i) (o.origin i) U)

/-- Each original mark retains its literal physical cutoff L, engineering
factor, and terminal label map. -/
theorem actual_log_physical (hLN : L ≤ N)
    (U : Config G (R.family.side L p)) :
    actualLog R N p L o d v U = Mach (Bud V) (fun i =>
      (R.family.S.a L : ℂ) ^ d i *
        R.family.O L p ((R.family.factory (d i) L p).terminal (v i))
          (o.origin i) U) := by
  unfold actualLog
  congr 1
  funext i
  exact congrFun (ActualRunPhysicalPages.kernel_physical R N p L (d i)
    hLN (v i) (o.origin i)) U

/-- The full unmasked marked density on the literal original representation. -/
def fullInput (U : Config G (R.family.side L p)) : Poly (Bud V) :=
  ((R.family.path.rep N p L).eval U : ℂ) •
    Poly.pass (actualLog R N p L o d v U)

def healthyLog (U : Config G (R.family.side L p)) : Poly (Bud V) :=
  Mach (Bud V) (fun i => masked (R.family.path.rep N p L).p.threshold
    (ActualRunPhysicalPages.cover R p L (d i) o i)
    (ActualRunPhysicalPages.kernel R N p L (d i) (v i) (o.origin i)) U)

theorem actual_log_split (U : Config G (R.family.side L p)) :
    actualLog R N p L o d v U = healthyLog R N p L o d v U +
      Mach (Bud V) (fun i => actualLeak R N p L o d v i U) := by
  unfold actualLog healthyLog Mach
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Extra.Trajectories.send_add]
  congr 1
  exact split_kernel _ _ _ U

/-- Complete equality before any coefficient extraction or expectation.  The
left side is the original vacuum times the UNMASKED actual marked product.
The right keeps the original healthy regular kernel and the full merged gas. -/
theorem actual_density_split (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L)
    (U : Config G (R.family.side L p)) :
    ((R.family.path.rep N p L).eval U : ℂ) •
      Poly.pass (actualLog R N p L o d v U) =
    (Real.exp ((R.family.path.rep N p L).exponent U) : ℂ) •
      (Poly.pass (healthyLog R N p L o d v U) *
        field (fun s => (actualInput R N p L o d v).forcedOutput
          (R.family.path.rep N p L).p.threshold s U)
          (flags (R.family.path.rep N p L).p.threshold U)) := by
  rw [actual_leak_field R N p L o d v hLN href U,
    actual_log_split R N p L o d v U]
  unfold healthyLog
  rw [Extra.Trajectories.pass_add (Accent.mute (Bud V) _)
    (Accent.mute (Bud V) _)]
  rw [← mul_assoc, mul_comm _ (Poly.bead (Bud V) _),
    Poly.product_bead, ← mul_smul, ← Complex.ofReal_mul]
  rfl

/-- Nonzero original forced coefficients are quiet.  Thus full stub transport
is needed only on an actual marked leak, whose original cover contains it. -/
theorem actual_toll_stubs :
    ∀ j U, ((actualInput R N p L o d v).deck
      (R.family.path.rep N p L).p.threshold).toll j U ≠ 0 →
      ∀ i ∈ ((actualInput R N p L o d v).deck
        (R.family.path.rep N p L).p.threshold).roster j,
        o.stub i ⊆ ((actualInput R N p L o d v).deck
          (R.family.path.rep N p L).p.threshold).cover j := by
  let Z := actualInput R N p L o d v
  let t := (R.family.path.rep N p L).p.threshold
  change ∀ j U, (Z.deck t).toll j U ≠ 0 →
    ∀ i ∈ (Z.deck t).roster j, o.stub i ⊆ (Z.deck t).cover j
  intro j U hn i hi
  cases j with
  | inl j =>
    have hp : (Z.regular j.1.val.1 U).part j.1.val.2 ≠ 0 := by
      intro hz
      apply hn
      change Z.piece t U j = 0
      unfold NativeCaptionDeck.Input.piece
      split
      · exact hz
      rfl
    have hm : j.1.val.2 = (Aged 0 V).fire (j.1.val.1, 0) := by
      by_contra hm
      exact hp ((Poly.part_send ..).trans (if_neg hm))
    change i ∈ (span j.1.val.2).val at hi
    rw [hm] at hi
    have he : i = j.1.val.1 := by simpa [span, Census.fire] using hi
    subst i
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  | inr j =>
    have hm : j.val.2 = (Aged 0 V).quiet := by
      by_contra hm
      apply hn
      change (bar (R.family.path.rep N p L).activities (Aged 0 V) U j.val.1).part
        j.val.2 = 0
      simp [bar, Poly.bead, hm]
    change i ∈ (span j.val.2).val at hi
    simp [hm, span, Census.quiet] at hi

theorem actual_output_stubs (s : Box (R.family.side L p))
    (U : Config G (R.family.side L p)) (q : (Bud V).Mode)
    (hq : ((actualInput R N p L o d v).forcedOutput
      (R.family.path.rep N p L).p.threshold s U).part q ≠ 0)
    (i : V) (hi : i ∈ q.val) : o.stub i ⊆ s.1 :=
  clay_stubs ((actualInput R N p L o d v).deck
    (R.family.path.rep N p L).p.threshold)
    (R.family.path.rep N p L).p.threshold o.stub
    (actual_toll_stubs R N p L o d v) s U q hq i hi

def actualCorrection (s : Box (R.family.side L p))
    (U : Config G (R.family.side L p)) : Poly (Bud V) :=
  (actualInput R N p L o d v).forcedOutput
    (R.family.path.rep N p L).p.threshold s U -
      bar (R.family.path.rep N p L).activities (Bud V) U s

theorem actual_correction_quiet (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L)
    (s : Box (R.family.side L p)) (U : Config G (R.family.side L p)) :
    (actualCorrection R N p L o d v s U).part (Bud V).quiet = 0 := by
  change ((actualInput R N p L o d v).forcedOutput _ s U).part (Bud V).quiet -
    (bar (R.family.path.rep N p L).activities (Bud V) U s).part (Bud V).quiet = 0
  rw [(actualInput R N p L o d v).quiet_preserved _
    (actual_input_admitted R N p L o d v hLN href) U s]
  simp [actualInput, bar, Poly.bead]

theorem actual_correction_stubs (s : Box (R.family.side L p))
    (U : Config G (R.family.side L p)) (q : (Bud V).Mode)
    (hq : (actualCorrection R N p L o d v s U).part q ≠ 0)
    (i : V) (hi : i ∈ q.val) : o.stub i ⊆ s.1 := by
  have hn : q ≠ (Bud V).quiet := by
    intro he
    simp [he, Census.quiet] at hi
  apply actual_output_stubs R N p L o d v s U q _ i hi
  intro hz
  apply hq
  change ((actualInput R N p L o d v).forcedOutput _ s U).part q -
    (bar (R.family.path.rep N p L).activities (Bud V) U s).part q = 0
  rw [hz]
  simp [bar, Poly.bead, hn]

end RetainedRun

section Difference
variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V]
    {B : Census V} {t : ℝ} {o : V → Site n} {s : Box n}
    {f g : Config G n → Poly B}

theorem flow_sub (hf : Flow o s f t) (hg : Flow o s g t) :
    Flow o s (fun U => f U - g U) t := by
  refine ⟨⟨fun U W hsites hflags => congrArg₂ (· - ·)
    (hf.home U W hsites hflags) (hg.home U W hsites hflags),
    fun a U => congrArg₂ (· - ·) (hf.turns a U) (hg.turns a U),
    fun q => (hf.me q).sub (hg.me q), fun U q hq => ?_⟩, ?_⟩
  · change (f U).part q - (g U).part q = 0
    rw [hf.scope U q hq, hg.scope U q hq, sub_self]
  intro U hu
  by_cases hh : f U = 0
  · apply hg.permits U
    intro he
    exact hu (by rw [hh, he, sub_self])
  exact hf.permits U hh

end Difference

section OriginalAddresses
variable {G : Gauge} (R : Run G) (N p L : ℕ)
    {V : Type} [DecidableEq V] [Fintype V]
    (o : Positions V (R.family.side L p)) (d : V → ℕ)
    (v : ∀ i, R.family.label (d i))

theorem actual_correction_flow (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L)
    (s : Box (R.family.side L p)) :
    Flow o.origin s (actualCorrection R N p L o d v s)
      (R.family.path.rep N p L).p.threshold := by
  apply flow_sub
  · exact (actualInput R N p L o d v).forced_output _
      (actual_input_admitted R N p L o d v hLN href) s
  exact Accent.granular (R.family.path.rep N p L).activities
    (R.family.path.rep N p L).p (Bud V)
    (R.makes.wilson.represents N p L hLN).good.labels s

/-- The full merged gas is re-expressed on the ORIGINAL Nat dictionary.  Its
countable old K is never replaced by the finite correction index. -/
theorem actual_original_gas (hG : G.Simple) (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L)
    (U : Config G (R.family.side L p)) :
    NativeForcedPolynomialReentry.gas
      (OriginalForcedAddresses.actual_keeper R hG N L p hLN)
      (actualCorrection R N p L o d v) U =
    field (fun s => (actualInput R N p L o d v).forcedOutput
      (R.family.path.rep N p L).p.threshold s U)
      (flags (R.family.path.rep N p L).p.threshold U) := by
  apply (NativeForcedPolynomialReentry.gas_eq
    (OriginalForcedAddresses.actual_keeper R hG N L p hLN)
    (actualCorrection R N p L o d v)
    (R.makes.wilson.represents N p L hLN).good.labels
    (w := fun _ => 1) (fun _ => zero_lt_one)
    (NativeForcedPolynomialReentry.flow_zero _ o.origin
      (actual_correction_flow R N p L o d v hLN href)) U).trans
  congr 1
  funext s
  change _ + (_ - _) = _
  abel

theorem actual_density_original_dictionary (hG : G.Simple) (hLN : L ≤ N)
    (href : ∀ i, R.family.ref (d i) ≤ L)
    (U : Config G (R.family.side L p)) :
    ((R.family.path.rep N p L).eval U : ℂ) •
      Poly.pass (actualLog R N p L o d v U) =
    (Real.exp ((R.family.path.rep N p L).exponent U) : ℂ) •
      (Poly.pass (healthyLog R N p L o d v U) *
        NativeForcedPolynomialReentry.gas
          (OriginalForcedAddresses.actual_keeper R hG N L p hLN)
          (actualCorrection R N p L o d v) U) := by
  rw [actual_original_gas R N p L o d v hG hLN href U]
  exact actual_density_split R N p L o d v hLN href U

end OriginalAddresses

end YM.Integration.ActualRunUnmaskedPartners
