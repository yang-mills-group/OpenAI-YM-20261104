import YM.Integration.SelectedCofactorInsertionPrice

/-! Finite marked punctures in the original pinned Wilson scalar vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorPuncturedVacuum
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic LocalComparison NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorJointBudget SelectedCofactorSupportBudget
open scoped Classical BigOperators Topology

variable {V : Type} [DecidableEq V] {B : Census V} {G : Gauge} {n : Side} {P : Rep G n}

private theorem low {α : Type*} [DecidableEq α] (t : Finset α) (f : α → Poly B)
    (hf : ∀ i ∈ t, (f i).part B.quiet = 0) (m : B.Mode) (hm : m.val.card < t.card) :
    (∏ i ∈ t, f i).part m = 0 := by
  induction t using Finset.induction_on generalizing m with
  | empty => simp at hm
  | @insert i t hi ih =>
    rw [card_insert_of_notMem hi] at hm
    rw [prod_insert hi,mul_comm,Poly.part_mul]
    refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
    split_ifs with h
    · by_cases e : b = B.quiet
      · rw [e,hf i (mem_insert_self ..),mul_zero]
      have hb : 0 < b.val.card := card_pos.mpr (nonempty_iff_ne_empty.mpr fun h => e (Subtype.ext h))
      have he : m.val.card = a.val.card + b.val.card := by rw [←h.2,card_union_of_disjoint h.1]
      rw [ih (fun j hj => hf j (mem_insert_of_mem hj)) a (by omega),zero_mul]
    · rfl

def changeRow (D : Deck B P) (U : Config G n) (j : ℕ) : Poly B :=
  D.contents.each j U - scalarRow P U j

def markedRow (D : Deck B P) (U : Config G n) (i j : ℕ) : Poly B :=
  if j < i then 0 else changeRow D U j

/-- Only the displayed finite punctures are marked. All other factors are the
original unmarked activities at their original Wilson addresses. -/
def component (D : Deck B P) (U : Config G n) (i : ℕ) (s t : Finset ℕ) : Poly B :=
  (∏ j ∈ insert i t, markedRow D U i j) * ∏ j ∈ s.erase i \ t, scalarRow P U j

theorem slices (D : Deck B P) (U : Config G n) (i : ℕ) (s : Finset ℕ) :
    term D U (i,s) =
      if admitted P U i s then ∑ t ∈ (s.erase i).powerset, component D U i s t else 0 := by
  rw [term,cofactor_eq_if]
  by_cases h : admitted P U i s
  · rw [if_pos h,if_pos h]
    change changeRow D U i * (∏ j ∈ s.erase i, if j < i then scalarRow P U j else D.contents.each j U) = _
    have hr (j : ℕ) : (if j < i then scalarRow P U j else D.contents.each j U) =
        markedRow D U i j + scalarRow P U j := by by_cases e : j < i <;> simp [markedRow,changeRow,e]
    simp_rw [hr]
    rw [Finset.prod_add,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hi : i ∉ t := fun e => (notMem_erase i s) (mem_powerset.mp ht e)
    rw [component,prod_insert hi,markedRow,if_neg (lt_irrefl i),mul_assoc]
  · simp only [if_neg h,mul_zero]

theorem vanishes (D : Deck B P) (U : Config G n)
    (h : ∀ j, (changeRow D U j).part B.quiet = 0) (i : ℕ) (s t : Finset ℕ)
    (ht : t ⊆ s.erase i) (m : B.Mode) (hm : m.val.card ≤ t.card) :
    (component D U i s t).part m = 0 := by
  have hi : i ∉ t := fun e => (notMem_erase i s) (ht e)
  have hz (j : ℕ) : (markedRow D U i j).part B.quiet = 0 := by
    by_cases e : j < i <;> simp only [markedRow,e,if_true,if_false,Poly.part_nil,h j]
  rw [component,Poly.part_mul]
  refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
  split_ifs with he
  · have hadd : m.val.card = a.val.card + b.val.card := by rw [←he.2,card_union_of_disjoint he.1]
    rw [low (insert i t) (markedRow D U i) (fun j _ => hz j) a (by rw [card_insert_of_notMem hi];omega),zero_mul]
  · rfl

/-- Each exact output mode has at most its own arity many marked addresses,
including the original distinguished root. -/
theorem mode (D : Deck B P) (U : Config G n) (h : ∀ j, (changeRow D U j).part B.quiet = 0)
    (i : ℕ) (s : Finset ℕ) (m : B.Mode) :
    (term D U (i,s)).part m =
      if admitted P U i s then ∑ t ∈ (s.erase i).powerset.filter (fun t => t.card < m.val.card),
        (component D U i s t).part m else 0 := by
  rw [slices]
  by_cases ha : admitted P U i s
  · rw [if_pos ha,if_pos ha,Poly.part_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hm : t.card < m.val.card
    · rw [if_pos hm]
    · rw [if_neg hm]
      exact vanishes D U h i s t (mem_powerset.mp ht) m (Nat.le_of_not_gt hm)
  · simp only [if_neg ha,Poly.part_nil]

variable [Fintype V] {E : Type*} {o : V → Site n} {T : Taste E o P B}
    {p : BudgetPoint} {w cost : V → ℝ} {κ reg fro : ℝ}

/-- The complete marked polynomial keeps a bounded number of punctures for
every field, even when the unchanged scalar spectator gas is arbitrarily large. -/
theorem finite (D : Deck B P) (U : Config G n) (h : ∀ j, (changeRow D U j).part B.quiet = 0)
    (i : ℕ) (s : Finset ℕ) :
    term D U (i,s) = if admitted P U i s then
        ∑ t ∈ (s.erase i).powerset.filter (fun t => t.card < Fintype.card V), component D U i s t
      else 0 := by
  rw [slices]
  by_cases ha : admitted P U i s
  · rw [if_pos ha,if_pos ha,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hm : t.card < Fintype.card V
    · rw [if_pos hm]
    · rw [if_neg hm]
      ext m
      exact (vanishes D U h i s t (mem_powerset.mp ht) m
        ((card_le_univ m.val).trans (Nat.le_of_not_gt hm))).trans (Poly.part_nil m).symm
  · simp only [if_neg ha]

/-- The actual funded residual has no additional unmarked perturbation at
any physical row. -/
theorem quiet (h : RelativeBudget p T w κ (envelopeProduct cost) reg fro)
    (hc : ∀ v, 0 < cost v) (x : E) (U : Config G n) (i : ℕ) :
    (changeRow (T.leaf x) U i).part B.quiet = 0 := by
  let D := T.leaf x
  have hs := tagged_summable h hc x i U
  have he : changeRow D U i = ∑' j, D.contents.tagged i j U := by
    unfold changeRow Bands.each scalarRow
    change (Poly.send B.quiet (P.activities.K i U : ℂ) + ∑' j, D.contents.tagged i j U) -
      Poly.send B.quiet (P.activities.K i U : ℂ) = _
    abel
  have hz (j : ℕ) : (D.contents.tagged i j U).part B.quiet = 0 := by
    rw [Bands.tagged,Poly.part_send,if_neg]
    exact fun he => ((h.budget.active x).articles.occurs i j).ne_empty (congrArg Subtype.val he.symm)
  change (changeRow D U i).part B.quiet = 0
  rw [he]
  exact (Poly.share (show Summable (fun j => D.contents.tagged i j U) from hs) B.quiet).trans
    ((tsum_congr hz).trans tsum_zero)

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorPacketIntegral SelectedCofactorConditionalSeries
open SelectedCofactorReplicatedFlags SelectedCofactorCommonVacuum SelectedCofactorJointBudget
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "μ₀" => prior G n₀

local notation "w₀" => (fun v => F.outputRadii v / F.kernelCosts v)
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level)
local notation "r₀" => Real.exp (Fintype.card V * ordinaryRate K I delta)
local notation "ε₀" => ((Fintype.card V : ℝ) * (forcedDivisor C datum.level *
    Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ^ forcedOrder))

/-- The physical selected signed term with precisely its admissible original
scalar spectators and at most one marked puncture per output mark. -/
theorem selected (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (U : Config G n₀) (i : ℕ) (s : Finset ℕ) (m : B.Mode) :
    let D := S.output.residual.leaf (testInclusion J.tests x)
    (term D U (i,s)).part m =
      if admitted S.output.carrier.rep U i s then
        ∑ t ∈ (s.erase i).powerset.filter (fun t => t.card < m.val.card), (component D U i s t).part m
      else 0 :=
  mode _ U (quiet H.residual_price F.kernel_positive x U) i s m

/-- The selected physical packet with all scalar spectators intact. -/
def pieces (S : Chosen K I M) (x : IndependentTests J.tests) (a : ℕ × Finset ℕ) (U : Config G n₀) : Poly B :=
  let D := S.output.residual.leaf (testInclusion J.tests x)
  if admitted S.output.carrier.rep U a.1 a.2 then
    ∑ t ∈ (a.2.erase a.1).powerset.filter (fun t => t.card < Fintype.card V),
      multiplier S x U * component D U a.1 a.2 t
  else 0

theorem pieces_eq (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (a : ℕ × Finset ℕ) (U : Config G n₀) :
    pieces S x a U = packet S x a U := by
  let D := S.output.residual.leaf (testInclusion J.tests x)
  have hpacket : packet S x a U = multiplier S x U * term D U a := mul_assoc ..
  rw [hpacket,finite D U (quiet H.residual_price F.kernel_positive x U) a.1 a.2]
  by_cases ha : admitted S.output.carrier.rep U a.1 a.2
  · simp only [pieces,ha,if_true,Finset.mul_sum,D]
  · simp only [pieces,ha,if_false,mul_zero]

end YM.Integration.SelectedCofactorPuncturedVacuum
end
