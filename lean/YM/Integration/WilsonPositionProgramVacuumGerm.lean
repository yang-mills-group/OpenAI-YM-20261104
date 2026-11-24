import YM.Integration.WilsonThermometerSubmittedMaterial
import YM.Integration.RunRG02Along

/-! At the top cutoff the measured layout was filed before all fields.
Its complete difference from the original positive Wilson vacuum is the
actual analytic plaquette remainder, including the kinetic reference. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramVacuumGerm
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Marker
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6
open PhysicalNext Repeat AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV
open Push Input Org AbsoluteSums PriceCompiler Roost Legato QuadraticLocal QuadraticLocal.Fk
open Comparison.RG02 WilsonStartup Stationary Exterior
open scoped BigOperators Classical ContDiff Topology

variable {G:Gauge} (R:Run G) {i m h p:ℕ}
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (book : PlanV.Path D R.alloy Q h (i+1) m π Γ)
    {V : Type} [DecidableEq V] (I:Census V)
    (X:Bulk.Colors I G (R.family.side (i+1) p))
set_option quotPrecheck false
local notation "old" => R.family.path.rep (i+1) p (i+1)
local notation "model" => Bare.bareUp I i p (H:=R.family.path) X
local notation "clip" => (R.alloy.B.a.params (i+1)).clip
local notation "acts" => R.alloy.B.kin.path (i+1) (i+1)
local notation "expense" g:max => Fk.money (π (i+1)) (Step.tape (h+2)) g

include book in
theorem registered (g:ℝ) (U:Config G (R.family.side (i+1) p)) :
    (expense g) U = Crest.scene clip h U := by
  rw [book.2.1]
  unfold Fk.money Crest.scene
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro age _
  exact Crest.gridV clip _ U g age

include book in
/-- The discrepancy of an arbitrary otherwise eligible R isolates exactly
the original dated kinetic choice. It does not follow merely from agreement
of two bare densities at one numerical coupling. -/
theorem separated (direct:(clip).direct≤1) (g:ℝ) (U:Config G (R.family.side (i+1) p)) :
    (model).vac g U - (expense g) U =
      Crest.margin clip h U + (mainTerm clip (Design.top G clip) U - mainTerm clip acts U) := by
  have hc : (old).clip=clip := ((R.T.sticks (i+1) p).prices (i+1) (Nat.zero_le _) le_rfl).1.clip
  have hp : (old).path=acts := ((R.T.sticks (i+1) p).prices (i+1) (Nat.zero_le _) le_rfl).1.path.trans
    (congrFun (congrFun R.alloy.B.bases (i+1)) (i+1))
  change Wilson.energy U - mainTerm (old).clip (old).path U - (expense g) U = _
  rw [hc,hp,registered R D Q π Γ book g U,Crest.funds clip h U direct]
  unfold Crest.picture
  ring

include book in
theorem original (paid:Extension.UV.Archive R.alloy.B) (g:ℝ) (U:Config G (R.family.side (i+1) p)) :
    (model).vac g U - (expense g) U = Crest.margin clip h U := by
  rw [separated R D Q π Γ book I X (paid.startup (i+1)).clip.direct,paid.top (i+1),sub_self,add_zero]

include book in
theorem projected (paid:Extension.UV.Archive R.alloy.B) :
    let n := R.family.side (i+1) p
    let residual := fun u : ℝ × fieldDir G n 1 =>
      Bulk.projected (model).vac u - Bulk.projected (fun g=>expense g) u
    ContDiffAt ℝ ω residual 0 ∧ FlatAt (h+5) residual 0 := by
  intro n residual
  let sample := fun u : ℝ × fieldDir G n 1 => (Stationary.arm G n 1).symm u.2
  have smooth : ContDiffAt ℝ ω sample 0 := by unfold sample; fun_prop
  have center : sample 0=0 := by unfold sample; exact map_zero _
  have physical : residual=(Crest.margin clip h ∘ Stationary.input G n) ∘ sample := by
    funext u
    change (model).vac u.1 (represent u.2) - (expense u.1) (represent u.2) =
      Crest.margin clip h (represent ((Stationary.arm G n 1) ((Stationary.arm G n 1).symm u.2)))
    rw [original R D Q π Γ book I X paid,(Stationary.arm G n 1).apply_symm_apply]
  rw [physical]
  obtain ⟨analytic,vanishes⟩ := Crest.margin_value (G:=G) clip n h
  have atCenter : ContDiffAt ℝ ω (Crest.margin clip h ∘ Stationary.input G n) (sample 0) :=
    center ▸ analytic
  refine ⟨atCenter.comp _ smooth,FlatAt.comp ?_ (atCenter.of_le le_top) ?_⟩
  · rw [center]; exact vanishes
  · exact smooth.of_le le_top

end YM.Integration.WilsonPositionProgramVacuumGerm
end

