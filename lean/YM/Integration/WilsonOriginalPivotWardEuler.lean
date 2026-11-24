import YM.Integration.WilsonOriginalPivotWardFaces

/-! A genuine compensated Wilson equation insertion with its complete filed clover spectator. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPivotWardEuler

open Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard XSpace
open WilsonOriginalPivotWardTree (heard viewer)
open scoped Classical BigOperators

variable {G : Gauge} {p : Period} (T : p.Tree) (b : Edge (Site p.side))

def direction (b : Edge (Site p.side)) (U : Config G p.side) : G.Color := WardBin.euler U b
theorem issued : Direction b (direction (G:=G) b) ∧ Approved b (direction (G:=G) b) 1 :=
  supplied_force (G:=G) (n:=p.side) (b:=b) (even_iff_two_dvd.mpr p.even)

variable {C : Family G} (data : C.Makes) (live : ∀ d, Bid.pop (C.localSection d))
    (i : (C.labels.level 4).Index) (atSite : Site p.side)

def mark := equationMark 1 b (direction (G:=G) b) * (viewer data live i atSite).couplingMark

/-- The same Euler stencil pays both its actual valuation and its complete nonquiet contact. -/
theorem original :
    let F := feed (G:=G) (even_iff_two_dvd.mpr p.even)
    let W := vertices G p.side
    let Q := viewer data live i atSite
    let K := mark b data live i atSite
    F.Funded (W.weight * K) ∧
      X^(2+Q.slots) * F.step W K = X^2 * heard T (coupled b (direction b) Q.stencil) := by
  intro F W Q K
  have grant := issued (G:=G) b
  have hp : Proxy Q.stencil := (onStamp data live
    (⟨4,le_rfl,i,atSite⟩ : Stamp.Reservation C p.side 4)).1
  have hh := keeps_debt (even_iff_two_dvd.mpr p.even) grant.1 grant.2 Q.test hp Q.atCoupling
  have eq : heard T (coupled b (direction b) Q.stencil) = replyCoeff (coupled b (direction b) Q.stencil) :=
    FVA2.BareOrb.diagram_eq T (grant.1.contact hp Q.test.gauge)
  rw [eq]
  exact hh

include T in
/-- This is zero after the actual inverse powers were restored on the finite inversion regulator. -/
theorem separated (clear : off b ((C.localSection 4).footprint atSite)) :
    let F := feed (G:=G) (even_iff_two_dvd.mpr p.even)
    F.step (vertices G p.side) (mark b data live i atSite) = 0 := by
  intro F
  let Q := viewer data live i atSite
  have got := (original T b data live i atSite).2
  have hp : Proxy Q.stencil := (onStamp data live
    (⟨4,le_rfl,i,atSite⟩ : Stamp.Reservation C p.side 4)).1
  have hl : LocalOn ((C.localSection 4).footprint atSite) Q.stencil := (onStamp data live
    (⟨4,le_rfl,i,atSite⟩ : Stamp.Reservation C p.side 4)).2
  have zero : heard T (coupled b (direction b) Q.stencil) = 0 := by
    have auth : heard T (coupled b (direction b) Q.stencil) = replyCoeff (coupled b (direction b) Q.stencil) :=
      FVA2.BareOrb.diagram_eq T ((issued (G:=G) b).1.contact hp Q.test.gauge)
    rw [auth, isolated b hl clear (direction b), reply_nil (G:=G) (even_iff_two_dvd.mpr p.even)]
  change X^(2+Q.slots) * F.step (vertices G p.side) (mark b data live i atSite) =
    X^2 * heard T (coupled b (direction b) Q.stencil) at got
  rw [zero, mul_zero] at got
  exact (mul_eq_zero.mp got).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)

end YM.Integration.WilsonOriginalPivotWardEuler
