import YM.Integration.WilsonOriginalPublicTwoTopJoined
import YM.Integration.WilsonOriginalPublicPivotSelf
import YM.Integration.WilsonOriginalPublicFigureWick
import YM.Integration.WilsonPositionProgramSubmittedCoordinates

/-! Use the very same finite compensated coordinate on both tops. The finite
basis bill includes lower fields and the unit, and is fixed before either cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicTwoTopInvoice
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramSubmittedCoordinates (submitted)
open WilsonOriginalPublicFigureWick (project)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped Topology BigOperators Classical
variable {G : Gauge} {a h e : ℕ} {I : Type} [Fintype I]

def letter (W : Initialize G) (F : Labels.Frame G h) {B : Local.Physical.Deck G}
    (γ : Glyph B h) : F.Coeff :=
  F.coords ((W.surveys h).insertW (-1) (On.sectionMap h (Daylight B h γ)))

theorem face (W : Initialize G) (F : Labels.Frame G h) {B : Local.Physical.Deck G}
    (γ : Glyph B h) : project W F (letter W F γ) = Daylight B h γ := by
  unfold WilsonOriginalPublicFigureWick.project WilsonOriginalPublicFigureWick.unwick letter
  simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]
  have w := (W.surveys h).wick_recovers (-1) (On.sectionMap h (Daylight B h γ))
  rw [neg_neg] at w
  rw [w]
  exact Subtype.ext (On.recovers _)

def stamp (W : Initialize G) (F : Labels.Frame G h) {B : Local.Physical.Deck G}
    (leg : I → Glyph B h) (x : I → ℂ) : F.Coeff :=
  ∑ i, x i • letter W F (leg i)
def bill (W : Initialize G) (F : Labels.Frame G h) {B : Local.Physical.Deck G}
    (leg : I → Glyph B h) : ℝ := ∑ i, F.coeffSize (letter W F (leg i))

theorem exact_stamp (W : Initialize G) (F : Labels.Frame G h) {B : Local.Physical.Deck G}
    (leg : I → Glyph B h) (x : I → ℂ) :
    project W F (stamp W F leg x) = ∑ i, x i • Daylight B h (leg i) := by
  simp only [stamp,map_sum,map_smul,face]

theorem charge (W : Initialize G) (F : Labels.Frame G h) {B : Local.Physical.Deck G}
    (leg : I → Glyph B h) (x : I → ℂ) :
    F.coeffSize (stamp W F leg x) ≤ ‖x‖*bill W F leg := by
  unfold Labels.Frame.coeffSize stamp bill
  calc
    _ ≤ ∑ j : F.Index, ∑ i : I, ‖x i‖ * ‖letter W F (leg i) j‖ := by
      apply sum_le_sum
      intro j _
      rw [Finset.sum_apply]
      simpa only [Pi.smul_apply,norm_smul] using
        norm_sum_le univ (fun i : I => x i • letter W F (leg i) j)
    _ ≤ ∑ j : F.Index, ∑ i : I, ‖x‖ * ‖letter W F (leg i) j‖ := by
      gcongr with j _ i _
      exact norm_le_pi_norm x i
    _ = _ := by rw [sum_comm]; simp only [← mul_sum,Labels.Frame.coeffSize]

variable (R : Run G)(W : Initialize G)(B : Local.Physical.Deck G)
    (l d : Fin (a+1) → ℕ)(fit : ∀ i,l i<d i)
    (I' : Fin (a+1) → Type) [∀ i,Fintype (I' i)] (leg : (i : Fin (a+1)) → I' i → Glyph B (l i))
    (x : (i : Fin (a+1)) → I' i → ℂ)(p : Fin (a+1) → ℂ →L[ℝ] ℝ)
def dose := submitted R l d fit (fun i => stamp W (R.family.labels.level (l i)) (leg i) (x i)) p

theorem original (e : ℕ) (i : Fin (a+1)) :
    let F := R.family.labels.level (l i)
    fee (dose R W B l d fit I' leg x p) e i ≤
      Fintype.card (Alma F)*(e+1:ℕ)*(‖p i‖*(‖x i‖*bill W F (leg i))) := by
  intro F
  apply (WilsonPositionProgramSubmittedCoordinates.paid R l d fit _ p e i).trans
  gcongr
  exact charge W F (leg i) (x i)

end YM.Integration.WilsonOriginalPublicTwoTopInvoice
end
