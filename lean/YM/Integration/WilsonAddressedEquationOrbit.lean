import YM.Integration.WilsonAddressedEquationReturn

/-! Restore the measured equation projector from the complete signed-axis
calibration on every independently chosen microscopic site. The finite
coefficient bill is fixed by the physical label space before both cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedEquationOrbit
open Finset Filter Lattice Wilson Labels RG Source Extra.Histories Extra.Histories.Motion
open MergeProof Push
open scoped Classical
set_option maxRecDepth 4096
variable {G:Gauge} {C:Family G} {d N p:ℕ} {V:SectionData (C.labels.level d)}
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "L"=> C.localSection d

private theorem painted {i:ℕ} (H:Labels.Frame G i) (U:H.Index→H.Coeff) (v:H.Coeff) :
    decor H U v=repaint H U v := by
  -- The native linear map has this function as its literal first projection.
  -- Supply kernel reflexivity without normalizing the complete frame instance in the elaborator.
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let .some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem restored (hC:C.Makes) (hV:V.Sound C.params)
    {P:C.label d≃ₗ[ℂ] C.label d} {U:(F).Index→C.label d}
    (file:∀v,P v=decor (F) U v) (v:C.label d) (o:Site (C.side N p)) :
    (∑ k:Tally (F),‖chips (F) v k‖) ≤ orbitCost (F)*(F).coeffSize v ∧
    ∀ A,initial (L) C.path N p (P v) o A - initial V C.path N p v o A =
      ∑ k:Tally (F),chips (F) v k * dance k.1
        (initial (L) C.path N p (U k.2) 0 -
          initial V C.path N p (Size.axis (F) k.2) 0) (Lattice.translate o A) := by
  refine ⟨chipcost (F) v,?_⟩
  let f := IsLinearMap.mk' _ (notationL C.path d (F) V N p 0)
  let g := IsLinearMap.mk' _ (notationL C.path d (F) (L) N p 0)
  have raw : g (P v)-f v = ∑ k:Tally (F), chips (F) v k •
      (g (Motion.patch (F) k.1 (U k.2))-f (Motion.patch (F) k.1 (Size.axis (F) k.2))) := by
    simp_rw [smul_sub,Finset.sum_sub_distrib,←map_smul,←map_sum]
    rw [file v,painted]
    change g (repaint (F) U v)-f v = g (repaint (F) U v)-f (repaint (F) (Size.axis (F)) v)
    rw [show repaint (F) (Size.axis (F)) v = v from repaint_same (F) LinearMap.id (fun _ _=>rfl) v]
  have spin (k:Tally (F)) :
      dance k.1 (g (U k.2)-f (Size.axis (F) k.2)) =
        g (Motion.patch (F) k.1 (U k.2))-f (Motion.patch (F) k.1 (Size.axis (F) k.2)) := by
    rw [show dance k.1 (g (U k.2)-f (Size.axis (F) k.2)) =
      dance k.1 (g (U k.2))-dance k.1 (f (Size.axis (F) k.2)) from
        funext fun A=>by unfold dance scalar; split <;> simp]
    exact congrArg₂ (·-·) (signed_intro C (L) (hC.sections d) N p k.1 (U k.2))
      (signed_intro C V hV N p k.1 (Size.axis (F) k.2))
  simp_rw [←spin] at raw
  intro A
  have atPoint (S:SectionData (F)) (x:C.label d) :
      initial S C.path N p x 0 (Lattice.translate o A)=initial S C.path N p x o A := by
    simp only [initial,Pi.smul_apply,SectionData.places_trans,zero_add]
  have reading := congrFun raw (Lattice.translate o A)
  simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at reading
  rw [←atPoint (L) (P v),←atPoint V v]
  exact reading

end YM.Integration.WilsonAddressedEquationOrbit
