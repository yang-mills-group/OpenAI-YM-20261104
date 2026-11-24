import YM.Integration.WilsonPositionProgramCopyTop
import YM.PertExtension.OrbLaurent

/-! The actual normalized top word on the chosen inversion tree starts at
the sum of the filed field ranks. No lower coefficient is discarded in the
rank division of a physical basis word. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramInversionRank
open Finset Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb
open PhysicalNext.Repeat.Legato Precision Series Series.Radial Series.Tested Chart
open scoped BigOperators Classical
open WilsonPositionProgramCopyTop
variable {G : Gauge} (C : Run G) (p : XSpace.Period)
    {I : Type} [Fintype I] [LinearOrder I] (d : I → ℕ) (z : I → Cover)
    (a : ∀ i,(C.family.labels.level (d i)).Index)

theorem radial :
    RadialOrder (Kick.depthF univ d a)
      (restrictedO (planted C p d z a) ∘ expLinks G (Cotree p.side)) := by
  intro A
  let x := fun i (t:ℝ) => SlotEvaluation.fieldAt (C.family.localSection (d i)) (a i)
    (wrap p.side (z i)) (representative (t • A))
  have bound := bill_product univ (fun i => ((C.family.labels.level (d i)).grades (a i)).2) x
    (fun i _ => (SlotEvaluation.pre_field (C.family.localSection (d i)) (C.makes.sections _)
       (Next.Foundations.valuation G _) (a i) (wrap p.side (z i))).2 A)
  change Bill _ (fun t => planted C p d z a (representative (t • A)))
  have equal : (fun t => planted C p d z a (representative (t • A))) = ∏ i, x i := by
    funext t
    change (∏ i, SlotEvaluation.fieldAt (C.family.localSection (d i)) (a i) (wrap p.side (z i)))
      (representative (t • A)) = (∏ i, x i) t
    simp only [Finset.prod_apply, x]
  rw [equal]
  exact bound

theorem original (T : p.Tree) (e : ℕ) (below : e < Kick.depthF univ d a) :
    PowerSeries.coeff e (normalized C p d z a T) = 0 := by
  rw [normalized,FVA2.XPos.genuine_X T (allowed C p d z a),PowerSeries.coeff_map,PowerSeries.coeff_mk]
  have vanishes := diag_down (traySpec G) (allowed C p d z a).curved (radial C p d z a)
    (even_iff_two_dvd.mpr p.even) e below
  rw [Orb.diag,vanishes,map_zero]

end YM.Integration.WilsonPositionProgramInversionRank
end
