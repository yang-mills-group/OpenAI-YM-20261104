import YM.Integration.ActualWilsonForcedGraph
import YM.Integration.OriginalForcedAddresses

/-! Rebooking a marked coefficient into the original Wilson forced slots.
The fixed level's support, inventory and budget are retained at every index. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonForcedSlots

open Function Set MeasureTheory Lattice Wilson RG Marker Source Labels
open Extra.Histories Relay Bid Planned.GuardedAtom MergeProof Trace.Physical
open Trace.Physical.GermGraph FullQLocal PhysicalNext.Repeat.Legato
open ActualWilsonGraphReclosure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} {X Y : Rep G n}

def address (X : Rep G n) (K : Guard.Keeper Y.p Y.activities) : ℕ ↪ ℕ where
  toFun i := K.code (sender X.activities i,i)
  inj' _ _ h := congrArg Prod.snd (K.code.injective h)

def place (X : Rep G n) (K : Guard.Keeper Y.p Y.activities) (q : Coefficient F n) :
    Coefficient F n :=
  { q with forced := extend (address X K) q.forced 0 }

theorem on_slot (K : Guard.Keeper Y.p Y.activities) (q : Coefficient F n) (i : ℕ) :
    (place X K q).forced (address X K i) = q.forced i :=
  (address X K).injective.extend_apply ..

theorem off_slot (K : Guard.Keeper Y.p Y.activities) (q : Coefficient F n) {i : ℕ}
    (h : i ∉ range (address X K)) : (place X K q).forced i = 0 :=
  extend_apply' _ _ _ h

/-- The original slot has the same support and inventory as the selected
partner, including when different partners share one footprint. -/
theorem barcode (K : Guard.Keeper Y.p Y.activities) (i : ℕ) :
    (Y.activities.forced (address X K i)).support = (X.activities.forced i).support ∧
    (Y.activities.forced (address X K i)).inventory = (X.activities.forced i).inventory :=
  ⟨K.support _, K.inventory _⟩

theorem format (K : Guard.Keeper Y.p Y.activities) (hp : X.p = Y.p)
    {o : Site n} {A : Hol G} {q : Coefficient F n} (h : q.Format o A X) :
    (place X K q).Format o A Y := by
  have fit (j : ℕ) : SlotFit Y o j ((place X K q).forced j) := by
    by_cases hj : j ∈ range (address X K)
    · obtain ⟨i,rfl⟩ := hj
      rw [on_slot]
      obtain ⟨hs,hi⟩ := barcode (X := X) K i
      refine ⟨h.invariant i, h.borel i, ?_, ?_, ?_⟩
      · rw [hs, ← hp]
        exact h.supported i
      · intro hq
        exact hs ▸ h.carried i hq
      intro U hq
      have held : (Y.activities.forced (address X K i)).support ∩ flags Y.p.threshold U =
          (Y.activities.forced (address X K i)).inventory := by
        rw [hs,hi,← hp]
        exact (h.forcing i U hq).1
      exact ⟨held, K.pass _ U held⟩
    rw [off_slot K q hj]
    exact slot_zero Y o j
  exact ⟨hp ▸ h.smooth, h.origin, h.identity_null, h.projects, fun i => (fit i).permits,
    fun i => (fit i).tagged, fun i => (fit i).invariant, fun i => (fit i).read,
    fun i => (fit i).borel⟩

/-- The complete original remainder budget is unchanged by the placement. -/
theorem price (K : Guard.Keeper Y.p Y.activities) (hp : X.p = Y.p)
    {o : Site n} {q : Coefficient F n} {κ r : ℝ} (h : q.remBound o X κ r) :
    (place X K q).remBound o Y κ r := by
  obtain ⟨a,b,ha,hb,hab,hκ,he,z,hz,ht⟩ := h
  let e := address X K
  let f : ℕ → ℝ := extend e z 0
  have atE (i : ℕ) : f (e i) = z i := e.injective.extend_apply ..
  have offE (j : ℕ) (hj : j ∉ range e) : f j = 0 := extend_apply' _ _ _ hj
  have hq (j : ℕ) : 0 ≤ f j ∧ ∀ U, ‖(place X K q).forced j U‖ ≤ f j := by
    by_cases hj : j ∈ range e
    · obtain ⟨i,rfl⟩ := hj
      rw [atE, on_slot]
      exact ht i
    rw [offE _ hj, off_slot K q hj]
    exact ⟨le_rfl, fun _ => (norm_zero (E := ℂ)).le⟩
  let fee (j : ℕ) := Y.p.mass (Y.activities.forced j).support (f j)
  have onFee (i : ℕ) : (fee ∘ e) i = X.p.mass (X.activities.forced i).support (z i) := by
    change Y.p.mass (Y.activities.forced (e i)).support (f (e i)) = _
    rw [atE, (barcode (X := X) K i).1, hp]
  have offFee (j : ℕ) (hj : j ∉ range e) : fee j = 0 := by
    simp only [fee, BudgetPoint.mass, offE _ hj, mul_zero]
  have hF : SumBudget (fee ∘ e) (κ*b) := (funext onFee).symm ▸ hz
  have hsup : Function.support fee ⊆ range e := by
    intro j hj
    by_contra hnot
    exact hj (offFee j hnot)
  refine ⟨a,b,ha,hb,hab,hκ,hp ▸ he,f,⟨fun j => (hq j).1.trans (Y.p.loMass _ _ (hq j).1),
    (e.injective.summable_iff offFee).mp hF.2.1,
    (e.injective.tsum_eq hsup).symm.trans_le hF.2.2⟩,hq⟩

section Original

variable (R : Run G) (hG : G.Simple) {N p i : ℕ} (hi : i ≤ N)
  (X : PhysicalCarrier R.family N p i)

def original (q : store R.family d p i) : store R.family d p i :=
  place X.rep (OriginalForcedAddresses.actual_keeper R hG N i p hi) q

/-- The actual selected slot has zero vacuum activity before insertion. -/
theorem original_blank (j : ℕ) :
    (R.family.path.rep N p i).activities.K
      (address X.rep (OriginalForcedAddresses.actual_keeper R hG N i p hi) j) = 0 :=
  Guard.Keeper.blank (R.tuning.receipts.samples hG N i p hi) (sender X.rep.activities j,j)

/-- The selected graph coefficient is represented on the fixed physical run
at precisely the original price, with the same regular part and germ. -/
theorem original_price (q : store R.family d p i)
    (hf : q.Format 0 R.family.params X.rep) {r : ℝ}
    (hr : q.remBound 0 X.rep (safety R.family i) r) :
    reads d N p i (original R hG hi X q) r ∧
      page d p i (original R hG hi X q) = page d p i q := by
  have hp := X.point.trans (R.makes.wilson.represents N p i hi).vac.symm
  exact ⟨⟨format _ hp hf, price _ hp hr⟩, rfl⟩

/-- After the actual placement, the residual density difference is precisely
the signed change of vacuum cofactors of the same marked amplitudes. -/
theorem original_difference (q : store R.family d p i)
    (he : X.rep.eval = (R.family.path.rep N p i).eval) (U : Config G (R.family.side i p)) :
    q.density 0 (R.family.localSection d) X.rep U -
      value d N p i (original R hG hi X q) U =
      gas X.rep q U - gas (R.family.path.rep N p i) (original R hG hi X q) U := by
  let Y := R.family.path.rep N p i
  have hp := X.point.trans (R.makes.wilson.represents N p i hi).vac.symm
  have hbase : q.exponentialEntry 0 (R.family.localSection d) X.rep U =
      (original R hG hi X q).exponentialEntry 0 (R.family.localSection d) Y U := by
    simp only [Coefficient.exponentialEntry, Coefficient.maskedTerm, original, place, hp, Y]
    rfl
  change q.density 0 (R.family.localSection d) X.rep U -
    (original R hG hi X q).density 0 (R.family.localSection d) Y U = _
  simp only [Coefficient.density, gas, hbase, he, Y]
  ring

end Original
end YM.Integration.ActualWilsonForcedSlots
