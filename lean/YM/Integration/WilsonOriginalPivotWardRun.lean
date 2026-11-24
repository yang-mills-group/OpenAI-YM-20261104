import YM.Integration.WilsonOriginalPivotWardProduct
import YM.FVAAlt2.Block.Starts

/-! Insert a compensated Euler direction into the actual finite public face, on its own course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPivotWardRun

open Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open XSpace XSpace.Rose XSpace.Cirrus PhysicalNext.Repeat.Legato
open WilsonOriginalPivotWardTree (viewer)
open WilsonOriginalPivotWardEuler (direction)
open WilsonOriginalPivotWardFaces (grades)
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (W : Initialize G)
variable (v : (i : Fin 2) → (R.family.labels.level (grades i)).Coeff)
    (P : (Y : Sample 2) → Fin 2 → Bare.Series (W.tree Y.F.p) G)
    (Y : Sample 2) (b : Edge (Site Y.F.p.side)) (i : (R.family.labels.level 4).Index)

def peer := viewer R.makes (FVAAlt2.Block.clothes R) i (chartV Y 1)

/-- Upper group function, with its divergence kept at the actual coupling lag. -/
def adjustment : Bare.Series (W.tree Y.F.p) G :=
  FVA2.BareOrb.stencil (W.tree Y.F.p) (effort b (direction b)) -
    Bare.scalar (W.tree Y.F.p) (PowerSeries.X^2) * FVA2.BareOrb.stencil (W.tree Y.F.p) (fallout b (direction b))

theorem component :
    let T := W.tree Y.F.p
    let Q := peer R Y i
    let F := feed (G:=G) (even_iff_two_dvd.mpr Y.F.p.even)
    let V := vertices G Y.F.p.side
    let K := WilsonOriginalPivotWardEuler.mark b R.makes (FVAAlt2.Block.clothes R) i (chartV Y 1)
    F.Funded (V.weight * K) ∧ Bare.normalized T G
      (adjustment W Y b * FVA2.BareOrb.stencil T Q.stencil) = X^(2+Q.slots) * F.step V K := by
  intro T Q F V K
  have h := (WilsonOriginalPivotWardEuler.issued (G:=G) b).1
  have seated := WilsonOriginalPivotWardEuler.original T b R.makes (FVAAlt2.Block.clothes R) i (chartV Y 1)
  refine ⟨seated.1,?_⟩
  calc
    _ = WilsonOriginalPivotWardTree.heard T (effort b (direction b) * Q.stencil) -
          X^2 * WilsonOriginalPivotWardTree.heard T (fallout b (direction b) * Q.stencil) := by
      unfold adjustment WilsonOriginalPivotWardTree.heard
      rw [sub_mul, mul_assoc, map_sub, Bare.normalized_scalar,
        WilsonOriginalPivotWardProduct.product T h.effort Q.test,
        WilsonOriginalPivotWardProduct.product T h.fallout Q.test]
    _ = X^2 * WilsonOriginalPivotWardTree.heard T (coupled b (direction b) Q.stencil) :=
      WilsonOriginalPivotWardTree.original T R.makes (FVAAlt2.Block.clothes R) i (chartV Y 1) h
    _ = _ := seated.2.symm

/-- Removing an enrolled equation from an arbitrary upper proxy leaves its actual peer error visible. -/
theorem original (z : PowerSeries ℂ) (offSite : off b ((R.family.localSection 4).footprint (chartV Y 1))) :
    let T := W.tree Y.F.p
    let C := Bare.scalar (G:=G) T z
    let E := adjustment W Y b
    let q := FVA2.BareOrb.stencil T (peer R Y i).stencil
    let H := WilsonOriginalPublicPivotFaces.raw R W grades v Y 0 - P Y 0
    WilsonOriginalPublicPivotFaces.part R W grades v P Y Finset.univ {0} =
      Bare.normalized T G ((H-C*E)*P Y 1) + z * Bare.normalized T G (E*(P Y 1 - q)) := by
  intro T C E q H
  have hp := (component R W Y b i).2
  rw [WilsonOriginalPivotWardEuler.separated T b R.makes (FVAAlt2.Block.clothes R) i (chartV Y 1) offSite,
    mul_zero] at hp
  rw [WilsonOriginalPivotWardFaces.opened]
  change Bare.normalized T G (H*P Y 1) = _
  rw [show H*P Y 1 = (H-C*E)*P Y 1 + C*(E*(P Y 1 - q)) + C*(E*q) by ring, map_add, map_add,
    Bare.normalized_scalar, Bare.normalized_scalar, hp, mul_zero, add_zero]

end YM.Integration.WilsonOriginalPivotWardRun
