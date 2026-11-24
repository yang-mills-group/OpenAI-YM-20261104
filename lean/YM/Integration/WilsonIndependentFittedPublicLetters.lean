import YM.Integration.WilsonIndependentFittedDirectoryNode
import YM.Integration.WilsonIndependentMatchedTopPublic

/-! The forward public field, on its original finite tree, down to the actual off-shell Wick letters. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedPublicLetters
open Finset Lattice XSpace XSpace.Rose XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonIndependentMatchedTopBasis (source)
open WilsonIndependentMatchedTopPublic (coefficients)
open WilsonOriginalPublicPlantedPivotFields (funds plant)
open scoped Classical BigOperators
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){n:ℕ}(Y:Sample n)(i:Fin n)

def placement:Sample 2:=⟨Y.F,fun _=>Y.layout i,Y.center⟩

def letter (d:ℕ)(v:Sec G d):Bare.Series (W.tree Y.F.p) G:=
  ∑k:Fin (d+1),(((Y.F.spacing:ℂ)^k.val)⁻¹) • source R W (placement Y i) (fun _=>k.val)
    (coefficients R W (fun _=>k.val) (fun _=>part d k.val v)) true 0

theorem actual (d:ℕ)(v:Sec G d):
    regal W d Y (chartV Y i) v=letter R W Y i d v:=by
  rw [regal,LinearMap.sum_apply]
  unfold letter
  apply sum_congr rfl
  intro k _
  exact WilsonIndependentMatchedTopPublic.original R W (placement Y i) (fun _=>k.val)
    (fun _=>part d k.val v) 0

variable (Z:WilsonPrescription G)(β:Deck G){d:ℕ}

def word (j:ℕ)(v:Sec G d):Bare.Series (Z.scheme.tree Y.F.p) G:=
  ∑a:Glyph β d,Bare.scalar (Z.scheme.tree Y.F.p) (funds β (WilsonPositionRawEpoch.matrix Z j d) v a)*
    letter R Z.scheme Y i d (Theater.Daylight β d a)

theorem restored (j:ℕ)(v:Sec G d):
    plant Z.scheme β (WilsonPositionRawEpoch.matrix Z j d) Y i v=word R Y i Z β j v:=by
  unfold plant word
  simp_rw [actual R Z.scheme Y i]

/-- A fitted full product on arbitrary real nodes uses the same raw Wilson letters,
including the unit and all weight components of every public axis. -/
theorem original (j:ℕ)(D:Fin n→Glyph β d→PowerSeries ℂ):
    WilsonIndependentFittedNumericalProduct.fitted Z.scheme Y
      (WilsonIndependentFittedDirectoryNode.arm Z β j Y) D =
    Bare.normalized (Z.scheme.tree Y.F.p) G
      (∏k,∑a,Bare.scalar (Z.scheme.tree Y.F.p) (D k a)*word R Y k Z β j (Theater.Daylight β d a)):=by
  simp only [WilsonIndependentFittedNumericalProduct.fitted,WilsonIndependentFittedDirectoryNode.arm,restored R]

end YM.Integration.WilsonIndependentFittedPublicLetters
