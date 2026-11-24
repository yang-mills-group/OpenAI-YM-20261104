import YM.Integration.WilsonPhysicalExteriorRichFarExtraction
import YM.Integration.WilsonMacroscopicRegisteredProbes

/-! The independent rich MS glyphs as genuine fields of the original
Wilson factory. At tree order their MS reading is exactly the original
free Maxwell class moment, at the prescribed positions and in the same
measure, before any extraction or change of frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFree
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Extraction Table Spec Climb Filter Set PhysMS
open scoped Classical Topology BigOperators
variable {G : Gauge} (C : Family G) (B : Deck G) {O : Booked B} {n : ℕ}

def basis (d : ℕ) : Module.Basis (Glyph B d) ℂ ((Bel C.book).Field d) :=
  (Daylight B d).map (exactField C.labels d).symm

theorem letters {d : ℕ} (a : Glyph B d) : writes C.labels d (basis C B d a)=Letters B a := by
  change (exactField C.labels d (basis C B d a)).val = _
  rw [basis,Module.Basis.map_apply,LinearEquiv.apply_symm_apply,readHeight]

/-- The canonical degree-truncated plane and original Maxwell hierarchy
give the same field moment for each independent rich word. -/
theorem free (M : MS_Data G O) {d : ℕ} (a : Fin n→Glyph B d) (x : Points n) (hx : x∈conf n) (μ : ℝ) :
    MSDeckProbeGram.raw M a x μ 0 = PhysMS.WickGoal (C:=C) (d:=fun _=>d) (basis C B d ∘ a) x := by
  change MSDeckProbeGram.raw M a x μ 0=visible C.labels d x (basis C B d ∘ a)
  unfold MSDeckProbeGram.raw Fountain.metric
  rw [Dial.highest_zero M μ x (FVA2.ColorCode.labelAt B ∘ a) hx,PositionX.visible_eq]
  congr 1
  funext i
  change Letters B (a i)=Maxwell.Free.address C.labels d (basis C B d (a i))
  exact (letters C B (a i)).symm

variable {f : Extraction.Order} {S : Table C.book}

/-- The existing original, leading field family sees precisely those
independently named rich order-zero entries on every separated compact. -/
theorem on_profile (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S) (L : PhysMS.Leading F J)
    (M : MS_Data G O) {d : ℕ} (a : Fin n→Glyph B d) (μ : ℝ) {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) :
    TendstoUniformlyOn (fun r=>PhysMS.measured F none (J r) (d:=fun _=>d) (basis C B d ∘ a) r)
      (fun x=>MSDeckProbeGram.raw M a x μ 0) Trace.Pilot.trail K := by
  let v : MaxwellSlots C (fun _ : Fin n=>d) := basis C B d ∘ a
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (L.lead n (fun _=>d) v 0 K hk sep) ε hε] with r read x hx
  have h := read x hx
  rw [dist_comm,dist_eq_norm] at h
  have jets : iteratedFDeriv ℝ 0 (PhysMS.measured F none (J r) v r) x-iteratedFDeriv ℝ 0 (WickGoal v) x=
      iteratedFDeriv ℝ 0 (PhysMS.measured F none (J r) v r-WickGoal v) x := by ext b; simp
  rw [jets,norm_iteratedFDeriv_zero] at h
  rw [free C B M a x (sep hx) μ,dist_comm,dist_eq_norm]
  exact h

end YM.Integration.WilsonMacroscopicRichFree
