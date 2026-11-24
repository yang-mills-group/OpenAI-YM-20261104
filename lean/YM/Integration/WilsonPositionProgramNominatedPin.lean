import YM.Integration.WilsonPositionProgramPinnedHearthHistory
import YM.Integration.WilsonMarkedIndependentNormalizedElection

/-! The pin is chosen on the actual capture lattice. All of its descendants
are translated together before any source is extracted or integrated. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramNominatedPin
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramPinnedHearthHistory
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {a h D k u e:ℕ}

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d fit) ≤ k):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∀ᶠ j:ℕ in atTop,∀m N b:ℕ,j ≤ m → m ≤ N → b ≤ N → ∀ X:Herit Q,∀φ:Wilt Q,∀y:ℝ,∀o:Cover,
      let top:=normalized L R.metals.O Q X m N
      let incoming:=HearthC Q L R.metals.O φ top m N N y
      cruises L R.metals.O N (capP Q) N b (shifted incoming (pin L.S b N o)) =
        shifted (LodeStar L R.metals.O φ top m b N y) o := by
  intro Q L
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded big rails l d fit cap]
    with j paid
  obtain ⟨W,Y,levels,ratio,_,start,_,_,_,_,enrolled⟩:=paid
  intro m N b late high seen X φ y o top incoming
  have authentic:Auth (capP Q) incoming := by
    have openNow:Y.L.V.anchor ≤ N := start ▸ late.trans high
    have issued:=Hearth_enter (m:=m) (y:=y) enrolled φ top openNow (le_refl N)
    rwa [levels,ratio] at issued
  have legal:Precision.LocalRatio R.metals.O:=ratio ▸ Y.L.V.green
  exact capture L simple legal incoming authentic o le_rfl seen

end YM.Integration.WilsonPositionProgramNominatedPin
end
