import YM.Integration.WilsonMovingCalibratedFields
import YM.RG17.Gathers

/-! The original calibrated reporting layout at unrounded fine coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingReportLedger
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Table
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (hG : G.Simple) {n : ℕ}
    {f : Extraction.Order} {S : Table R.family.book} {F : Spec.Final R.family f S}

include hG in
theorem original (L : Layout F) (r : ℝ) (d : Caps n) (w : R.family.book.Vector d)
    (ref : ∀ j, R.family.ref (d j) ≤ L.level r)
    (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ×ℕ in L.lens, ∀ z : Positions n, tag (R.family.S.a i.1) z ∈ K →
      dist (R.family.numeric i.1 i.2 (fun j=>⟨d j,RG17.atRef L (d j) r i (w j)⟩) (wrap _ ∘ z))
        (S.classMoment S d (tag (R.family.S.a i.1) z) (fun j=>RG17.master L (d j) r (w j))) < ε := by
  letI := L.notbot
  let c (j : Fin n) := locatedRef L (d j) r (w j)
  let t (i : ℕ×ℕ) (j : Fin n) := atRef L (d j) r i (w j)
  have motion (j : Fin n) : Tendsto (fun i=>t i j) L.lens (𝓝 (c j)) :=
    tendsRef L le_rfl (v:=fun _=>w j) tendsto_const_nhds (ref j)
  have paid := WilsonMovingCalibratedFields.paid R hG F L.certified d t c motion K hk sep ε he
  filter_upwards [paid] with i buy z hz
  have eq : S.value d (tag (R.family.S.a i.1) z) c =
      S.classMoment S d (tag (R.family.S.a i.1) z) (fun j=>master L (d j) r (w j)) := by
    simp_rw [←payRef]
    exact (S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (sep hz) (fun j=>⟨d j,c j⟩)).symm
  rw [←eq]
  exact buy z hz

end YM.Integration.WilsonMovingReportLedger
