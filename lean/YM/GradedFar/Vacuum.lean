import YM.GradedFar.FormalDemand
import YM.GradedFar.RoseSub

/-! For reading masked arrays as subarray requests (or vice versa), the actual unit rule.
Carry from the Galop prescription and Gate limit as in FormalDemand. -/
namespace YM.FVA2.GradedFar.Subarray
noncomputable section
open Set Filter Function Real PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m : ℕ} {N : WilsonPrescription G} {simple : G.Simple}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)
  (w : Fin m ↪ Fin n) (d : ℕ)
local notation "Y" => N.scheme
local notation "κ" => N.criterion

lemma status_unit (F : ℕ → Point G d n) (Q : ℕ → Point G d m) (B : Guard G d)
    (h : ∀ k (u : Tags G d n), (∀ i ∉ range w, u i = leaf G d) → F k u = Q k (u ∘ w))
    (hb : ∀ k, coeff k B (leaf G d) = if k=0 then leaf G d else 0)
    (v : Tags G d n) (hv : ∀ i ∉ range w, v i = leaf G d) (j : ℕ) :
    Dframe.status B F j v = Dframe.status B Q j (v ∘ w) := by
  rw [seen,seen]
  exact dates_kernel w (fun i k => coeff k B (v i)) (fun i hi k => by rw [hv i hi, hb]) F Q h j


include H
lemma start_unit (z : Scale.Stage n) (v : Tags G d n)
    (hv : ∀ i ∉ range w, v i = leaf G d) (j : ℕ) : Scale.Measure.start Y κ d n z j v =
    Scale.Measure.start Y κ d m ⟨config w z.val, configuration w z.property⟩ j (v ∘ w) := by
  have h := (H.startsInX d m ⟨config w z.val,configuration w z.property⟩ j (v ∘ w)).comp
    (gate w z.val)
  exact tendsto_nhds_unique (H.startsInX d _ z j v) (h.congr fun p => (measureX_unit w d Y κ p v hv j).symm)

theorem book_unit (z : Scale.Stage n) (v : Tags G d n) (hv : ∀ i ∉ range w, v i = leaf G d) (j : ℕ) :
    book N d n z j v = book N d m ⟨config w z.val, configuration w z.property⟩ j (v ∘ w) := by
  have h := (H.details.toServed.toPosted.toQuoted.toContract.joint (Teller.logNu 1) d).2.2.scale
  exact status_unit w _ _ _ (Scale.Measure.adjust Y κ d)
    (fun k u h => start_unit H w d z u h k) (fun k => by
      split_ifs with he
      · subst k; rw [h.zero, Module.End.one_apply]
      exact (h.high k he).1) v hv j
omit H
lemma status_empty (F : ℕ → Point G d 0) (B : Guard G d)
    (v : Tags G d 0) (j : ℕ) : status B F j v = F j v := by
  rw [seen]
  exact empty_slots (fun i k => coeff k B (v i)) v F j

include H
theorem book_empty (z : Scale.Stage 0) (v : Tags G d 0) (j : ℕ) : book N d 0 z j v = coeff j 1 := by
  change status _ _ j v = _
  rw [status_empty d (Scale.Measure.start Y κ d 0 z)]
  exact tendsto_nhds_unique (H.startsInX d 0 z j v) (tendsto_const_nhds.congr fun q =>
    (measureX_empty d Y κ q v j).symm)
end
end YM.FVA2.GradedFar.Subarray
