import YM.Integration.WilsonOriginalPublicPivotFaces
import YM.FVA2.BareOrb
import YM.FormalOPE.RG10.Ward.Quotient

/-! A compensated Ward insertion and its spectator contact on the chosen inversion tree. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPivotWardTree

open Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard XSpace
open scoped Classical BigOperators

variable {G : Gauge} {p : Period} (T : p.Tree)

def heard (O : Config G p.side → ℝ) : PowerSeries ℂ :=
  Bare.normalized T G (FVA2.BareOrb.stencil T O)

private theorem orbit {O : Config G p.side → ℝ} (ho : PreTest O) :
    heard T O = replyCoeff O := FVA2.BareOrb.diagram_eq T ho

variable {b : Edge (Site p.side)} {Z : Config G p.side → G.Color}

/-- Both true Wilson force terms retain the entire spectator. Their difference is its contact. -/
theorem contact (h : Direction b Z) {O : Config G p.side → ℝ}
    (ho : Proxy O) (inv : respects O) :
    heard T (effort b Z * O) - X^2 * heard T (fallout b Z * O) =
      X^2 * heard T (coupled b Z O) := by
  rw [orbit T (Uses.pre_mul h.effort (ho.active inv)),
    orbit T (Uses.pre_mul h.fallout (ho.active inv)), orbit T (h.contact ho inv),
    reply_relation (even_iff_two_dvd.mpr p.even) b h ho inv]
  ring

variable {C : Family G} (data : C.Makes) (live : ∀ d, Bid.pop (C.localSection d))
    (i : (C.labels.level 4).Index) (site : Site p.side)

def viewer : Stamp G p.side :=
  Stamp.placed C data live (⟨4,le_rfl,i,site⟩ : Stamp.Reservation C p.side 4)

/-- Specialize to the real observable of the declared original weight-four stencil. -/
theorem original (h : Direction b Z) :
    let f := (viewer data live i site).stencil
    heard T (effort b Z * f) - X^2 * heard T (fallout b Z * f) =
      X^2 * heard T (coupled b Z f) := by
  have placed := onStamp data live (⟨4,le_rfl,i,site⟩ : Stamp.Reservation C p.side 4)
  exact contact T h placed.1 (viewer data live i site).test.gauge

/-- Holding both the updating link and its inverted image off the filed stencil kills its contact. -/
theorem separated (h : Direction b Z) (clear : off b ((C.localSection 4).footprint site)) :
    let f := (viewer data live i site).stencil
    heard T (effort b Z * f) - X^2 * heard T (fallout b Z * f) = 0 := by
  have placed := onStamp data live (⟨4,le_rfl,i,site⟩ : Stamp.Reservation C p.side 4)
  have hp : Proxy (viewer data live i site).stencil := placed.1
  have hs : LocalOn ((C.localSection 4).footprint site) (viewer data live i site).stencil := placed.2
  have hh := original T data live i site h
  dsimp only at hh ⊢
  rw [hh, orbit T (h.contact hp (viewer data live i site).test.gauge),
    isolated b hs clear Z, reply_nil (G:=G) (even_iff_two_dvd.mpr p.even), mul_zero]

end YM.Integration.WilsonOriginalPivotWardTree
