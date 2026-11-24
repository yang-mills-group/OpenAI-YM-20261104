import YM.Integration.WilsonMovingCalibratedFields
import YM.RG17.Gathers

/-! Separate true calibration radii for microscopic sources and fixed macroscopic detector legs, on the identical reporting layout and numerical law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMixedScaleReportLedger
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Table
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (hG : G.Simple) {n : ℕ}
    {f : Extraction.Order} {S : Table R.family.book} {F : Spec.Final R.family f S}

include hG in
theorem original (L : Layout F) (s : Fin n→ℝ) (d : Caps n) (w : R.family.book.Vector d)
    (ref : ∀ j, R.family.ref (d j) ≤ L.level (s j))
    (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ×ℕ in L.lens, ∀ z : Positions n, tag (R.family.S.a i.1) z ∈ K →
      dist (R.family.numeric i.1 i.2 (fun j=>⟨d j,RG17.atRef L (d j) (s j) i (w j)⟩) (wrap _ ∘ z))
        (S.classMoment S d (tag (R.family.S.a i.1) z) (fun j=>RG17.master L (d j) (s j) (w j))) < ε := by
  letI := L.notbot
  let c (j : Fin n) := locatedRef L (d j) (s j) (w j)
  let t (i : ℕ×ℕ) (j : Fin n) := atRef L (d j) (s j) i (w j)
  have motion (j : Fin n) : Tendsto (fun i=>t i j) L.lens (𝓝 (c j)) :=
    tendsRef L le_rfl (v:=fun _=>w j) tendsto_const_nhds (ref j)
  have paid := WilsonMovingCalibratedFields.paid R hG F L.certified d t c motion K hk sep ε he
  filter_upwards [paid] with i buy z hz
  have eq : S.value d (tag (R.family.S.a i.1) z) c =
      S.classMoment S d (tag (R.family.S.a i.1) z) (fun j=>master L (d j) (s j) (w j)) := by
    simp_rw [←payRef]
    exact (S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (sep hz) (fun j=>⟨d j,c j⟩)).symm
  rw [←eq]
  exact buy z hz

include hG in
/-- Cutoff and continuum differences use the very same fixed labels and
spatial array on the unchanged exterior. The two physical site arrays
may themselves depend on the regulator. -/
theorem difference (L : Layout F) (s : Fin n→ℝ) (d : Caps n) (w : R.family.book.Vector d)
    (ref : ∀ j,R.family.ref (d j) ≤ L.level (s j))
    (K:Set (Points n)) (hk:IsCompact K) (sep:K⊆conf n) {ε:ℝ} (he:0<ε) :
    ∀ᶠ i:ℕ×ℕ in L.lens,∀ z t:Positions n, tag (R.family.S.a i.1) z∈K →
    tag (R.family.S.a i.1) t∈K →
    let physical := fun y:Positions n=>R.family.numeric i.1 i.2
      (fun j=>⟨d j,atRef L (d j) (s j) i (w j)⟩) (wrap _ ∘ y)
    let fixed := fun y:Positions n=>S.classMoment S d (tag (R.family.S.a i.1) y)
      (fun j=>master L (d j) (s j) (w j))
    ‖(physical z-physical t)-(fixed z-fixed t)‖ < 2*ε := by
  filter_upwards [original R hG L s d w ref K hk sep ε he] with i yes z t hz ht
  dsimp only
  have a:=yes z hz; have b:=yes t ht
  rw [dist_eq_norm] at a b
  generalize R.family.numeric i.1 i.2 (fun j=>⟨d j,atRef L (d j) (s j) i (w j)⟩) (wrap _ ∘ z)=p at a ⊢
  generalize R.family.numeric i.1 i.2 (fun j=>⟨d j,atRef L (d j) (s j) i (w j)⟩) (wrap _ ∘ t)=q at b ⊢
  generalize S.classMoment S d (tag (R.family.S.a i.1) z) (fun j=>master L (d j) (s j) (w j))=u at a ⊢
  generalize S.classMoment S d (tag (R.family.S.a i.1) t) (fun j=>master L (d j) (s j) (w j))=v at b ⊢
  rw [show (p-q)-(u-v)=(p-u)-(q-v) by ring]
  exact (norm_sub_le _ _).trans_lt (by linarith)

end YM.Integration.WilsonMixedScaleReportLedger


