import YM.Integration.WilsonPositionProgramRayChart

/-! The same independently translated root is evaluated in the exact inversion
tree coordinates. Both reflected and retained bonds enter its finite input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramInvertedStencil
open Set Filter Function Finset Matrix RG Lattice PhysicalNext.Repeat.Legato Source
open Precision Wilson XSpace RegulatorIR.FVAAlt2 PertExtension
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank PertExtension.Orb
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} {p : Period} (T : p.Tree)

def tangent : T.Field G →L[ℝ] Lawn (Woods G p.side) :=
  (cloth G p.side).toContinuousLinearMap.comp T.logdir.toContinuousLinearMap

theorem coordinates (v : T.Field G) : mantle (tangent (G:=G) T v) = T.links v := by
  change Precision.represent ((cloth G p.side).symm ((cloth G p.side) (T.logdir v))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply,T.represent_eq]

def packet : Ink (Woods G p.side) →+* Bare.Series T G :=
  WilsonPositionProgramRayChart.pull (T.basis G) (tangent T)

def moved (R : Run G) (d : ℕ) (u : (R.family.labels.level d).Index) (z : Cover) :
    Lawn (Woods G p.side) → ℝ := fun v => Plies (R.family.localSection d) u p.side
      (Matrix.mulVec (spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side)) v)

theorem curved (R : Run G) (d : ℕ) (u : (R.family.labels.level d).Index) (z : Cover) :
    Green (moved (p:=p) R d u z) := by
  let m := spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side)
  have origin : m *ᵥ (0:Lawn (Woods G p.side)) = 0 := Matrix.mulVec_zero m
  have h : ContDiffAt ℝ ω (Plies (R.family.localSection d) u p.side) (m *ᵥ 0) := by
    rw [origin]
    exact innu _ R.family.params (R.makes.sections d) u p.side
  exact h.comp 0 (board m)

theorem submitted (R : Run G) (d : ℕ) (u : (R.family.labels.level d).Index) (z : Cover) (v : T.Field G) :
    moved R d u z (tangent T v) =
      SlotEvaluation.fieldAt (R.family.localSection d) u (wrap p.side z) (T.links v) := by
  change ((R.family.localSection d).places (Pi.single u 1) 0 (mantle (_ *ᵥ tangent T v))).re = _
  rw [mantle_reads, Lattice.pull_one,coordinates,SectionData.places_trans,zero_add]
  rfl

theorem original (R : Run G) (d : ℕ) (u : (R.family.labels.level d).Index) (z : Cover) :
    packet T (loom (spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side))
      (jet (Plies (R.family.localSection d) u p.side))) =
      Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘
        (SlotEvaluation.fieldAt (R.family.localSection d) u (wrap p.side z) ∘ T.links)) := by
  let K := spear (jog (wrap p.side z) : Woods G p.side ≃ Woods G p.side)
  let f := Plies (R.family.localSection d) u p.side
  have hf : Green f := innu (R.family.localSection d) R.family.params (R.makes.sections d) u p.side
  change packet T (loom K (jet f)) = _
  rw [loom_jet K f hf]
  change packet T (jet (moved R d u z)) = _
  have matchf : moved R d u z ∘ tangent T = SlotEvaluation.fieldAt (R.family.localSection d) u (wrap p.side z) ∘ T.links :=
    funext fun x => submitted T R d u z x
  rw [packet,WilsonPositionProgramRayChart.original _ _ _ (curved R d u z),matchf]

end YM.Integration.WilsonPositionProgramInvertedStencil
end
