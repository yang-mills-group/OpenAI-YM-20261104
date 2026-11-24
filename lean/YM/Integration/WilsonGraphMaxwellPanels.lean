import YM.UVNext.FREE_STRESS_CERTIFICATE.Rest
import YM.Next.MAXWELL.System

/-! The filed curvature pairs in the public Maxwell shell of the Ward tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress.PublicPanels
open Maxwell Labels Climb Table Work.A01 Next.UVStress
open scoped BigOperators
variable {G : Gauge} (F : Frames G)

theorem embedded {d : ℕ} (p : Label G d) :
    Free.address F d (embed F d p) = observable G d p := by
  rw [Free.address_eval]
  change ((Free.fields F d) ((freeTable F).project d ((F.level d).coords p))).val = _
  rw [Free.fields_eval]
  change observable G d ((F.level d).coords.symm ((F.level d).coords p)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem unitAddress : Free.address F 4 ((freeTable F).unit 4) = 1 := by
  rw [← pin_unit F 4, embedded]
  exact map_one reduceEq

theorem flatAddress (a b c e : Axis) :
    Free.address F 4 (flat F a b c e) = Free.phi (G := G) a c b e := by
  have atZero (i j : Axis) (k : G.ColorIndex) :
      curlProbe (G := G) (initialPlace i j) k = Free.omegaLeg k i j := by
    change constrain (fromF G (YM.basis ∘ (Fin.elim0 : Fin 0 → Axis)) k i j) =
      constrain (fromF G (fun _ => 0) k i j)
    rw [Subsingleton.elim (YM.basis ∘ (Fin.elim0 : Fin 0 → Axis)) (fun _ => (0 : E4))]
  change Free.address F 4 (embed F 4 (ff G 4 le_rfl a b c e)) = _
  simp only [embedded, ff, shell_bond, Free.phi, atZero]

theorem panelAddress (i j : Axis) :
    Free.address F 4 (panel F i j) = Free.sheetEnergy (G := G) i j := by
  simp only [panel, Free.sheetEnergy, map_sum, flatAddress]

theorem totalAddress :
    Free.address F 4 (total F) = ∑ i : Axis, Free.sheetEnergy (G := G) i i := by
  simp only [total, Free.sheetEnergy, map_sum, flatAddress]

end YM.UVNext.FreeStress.PublicPanels

