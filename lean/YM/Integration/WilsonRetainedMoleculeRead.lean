import YM.Integration.ManuscriptQLocalHealthyMoments
import YM.MergeProof.Palette

/-! Read each genuine signed molecular activity on its own accepted support,
with its full inherited and fresh team under the original two tag averages. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRetainedMoleculeRead
open Function Finset Lattice Wilson RG Tree Pressure Pressure.Stores ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums Push.SectorMeasure
open PhysicalNext PhysicalNext.Repeat Greenbelt Lotus Daisy RGLocalTaylor
open Merge Integration.ManuscriptQLocalHealthyMoments
open scoped Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ α : ℝ}
    {o : Target.Order G W} (H : Cash W s μ L Q o α T R) (χ : Chi)
    {ι : Type} (rows : ι → Leaf R)

/-- The full, locally masked Haar and Gaussian integral. Its exterior is
left at the supplied compact configuration. -/
def localRead (p : H.ThinP) (k : Tickets (Merge.Palette.sign rows S)) (U : Config G c) : ℝ :=
  let A:=Merge.Palette.team rows k
  if authorized H p.val ∧ A.signs S ⊆ p.val then
    RG.masked (Pressure.temp s) (H.unionP p.val)
      (measured (Mayer.original H p.val (p.val \ A.signs S) (Laminate.partner A H)) H χ p.val) U
  else 0

variable {j n : ℕ} {C' d v Y A b r B q : ℝ} (N : Captain H j C' d v Y A b r B q n χ)
include N

theorem factor (p : H.ThinP) (k : Tickets (Merge.Palette.sign rows S)) (U : Config G c) :
    Merge.Palette.act rows H χ U p.val k = localRead H χ rows p k U := by
  let team:=Merge.Palette.team rows k
  by_cases h : authorized H p.val ∧ team.signs S ⊆ p.val
  · rw [localRead,if_pos h]
    exact ManuscriptQLocalHealthyMoments.team (N:=N) (permit:=h.1) (unflagged:=p.2.2) team h.2 U
  rw [localRead,if_neg h]
  by_contra observed
  let F : Forest S.ratio := Classical.choice (Tree.select S.ratio S.patch.odd_side)
  obtain ⟨placed,stands⟩ := Merge.Palette.present rows H χ U k p.val (F:=F) observed
  apply h
  exact ⟨⟨stands.1,stands.2.1⟩,(Merge.Palette.label rows k).symm ▸ placed⟩

end YM.Integration.WilsonRetainedMoleculeRead
