import YM.Integration.WilsonOriginalPivotWardTree

/-! Isolate the Ward response and a physical lower-field variation on the original (6,4) pivot face. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPivotWardFaces

open Lattice RG Wilson Source Labels PowerSeries XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus
open XSpace.Structure1 PhysicalNext.Repeat.Legato FormalOPE.RG10.InversionWard
open WilsonOriginalPublicPivotFaces (part raw)
open WilsonOriginalPivotWardTree (heard viewer)
open scoped Classical BigOperators

def grades : Fin 2 → ℕ := ![6, 4]

variable {G : Gauge} (R : Run G) (W : Initialize G)
    (v : (i : Fin 2) → (R.family.labels.level (grades i)).Coeff)
local notation "T" X:max => W.tree (X : Sample 2).F.p
local notation "Bank" => (X : Sample 2) → Fin 2 → Bare.Series (T X) G

def insert (P : Bank) (X : Sample 2) : Bare.Series (T X) G :=
  (raw R W grades v X 0 - P X 0) * P X 1

theorem opened (P : Bank) (X : Sample 2) :
    WilsonOriginalPublicPivotFaces.part R W grades v P X Finset.univ {0} = Bare.normalized (T X) G (insert R W v P X) := by
  have complement : (Finset.univ \ {0} : Finset (Fin 2)) = {1} := by decide
  simp [WilsonOriginalPublicPivotFaces.part, insert, complement]

/-- The whole product of the filed variation with the actual viewer is decomposed before normalization. -/
theorem ward (P : Bank) (X : Sample 2) {b : Edge (Site X.F.p.side)}
    {Z : Config G X.F.p.side → G.Color} (direction : Direction b Z)
    (stock : ∀ d, Bid.pop (R.family.localSection d))
    (i : (R.family.labels.level 4).Index) :
    let tree := W.tree X.F.p
    let f := (viewer R.makes stock i (chartV X 1)).stencil
    let eqn := FVA2.BareOrb.stencil tree (effort b Z * f) -
      Bare.scalar (G:=G) tree (PowerSeries.X^2) * FVA2.BareOrb.stencil tree (fallout b Z * f)
    WilsonOriginalPublicPivotFaces.part R W grades v P X Finset.univ {0} =
      Bare.normalized tree G (insert R W v P X - eqn) + PowerSeries.X^2 * heard tree (coupled b Z f) := by
  intro tree f eqn
  have joined := WilsonOriginalPivotWardTree.original tree R.makes stock i (chartV X 1) direction
  change heard tree (effort b Z * f) - PowerSeries.X^2 * heard tree (fallout b Z * f) =
    PowerSeries.X^2 * heard tree (coupled b Z f) at joined
  rw [opened, map_sub, ← joined]
  dsimp only [eqn,heard]
  rw [map_sub, Bare.normalized_scalar]
  abel

/-- The spectator has its genuine own-horizon on-shell section, finite mesh factor and Wick completion. -/
def bank (upper : (X : Sample 2) → Bare.Series (T X) G) (peer : On.Grade G 4) : Bank :=
  fun X i => if i = 0 then upper X else W.atSite X.F 4 (chartV X 1) peer

/-- A change of the upper by a lower field contributes its complete normalized two-field response. -/
theorem lower (upper : (X : Sample 2) → Bare.Series (T X) G)
    (added peer : On.Grade G 4) (c : PowerSeries ℂ) (X : Sample 2) :
    WilsonOriginalPublicPivotFaces.part R W grades v (bank W upper peer) X Finset.univ {0} -
      WilsonOriginalPublicPivotFaces.part R W grades v (bank W (fun Y => upper Y +
        Bare.scalar (G:=G) (T Y) c * W.atSite Y.F 4 (chartV Y 0) added) peer) X Finset.univ {0} =
      c * Bare.normalized (T X) G (W.atSite X.F 4 (chartV X 0) added *
        W.atSite X.F 4 (chartV X 1) peer) := by
  rw [opened, opened, ← map_sub, ← Bare.normalized_scalar]
  congr 1
  simp [insert, bank]
  ring

end YM.Integration.WilsonOriginalPivotWardFaces
