import YM.Integration.FVA1Physical.Round2.CircuitWilson
import YM.Integration.FVA1Physical.Round2.CalibratedEnvelope

/-! Uniform actual vacuum estimates through the full retained history, with
the independent formal action identified at the first non-bare level on
that very scene. The choice of the scene precedes every source test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Filter RG Lattice YM.Wilson Exterior Tree Marker PhysicalNext.Repeat.Legato Comparison.RG02
open MSbar MSbar.Rolling MSbar.Wave MSbar.Midpoint Push Push.Uniform Precision
open MSbar.Lis MSbar.Whisk MSbar.CrossH FormalOPE.RG10.InversionTop
open scoped Classical Matrix.Norms.Frobenius Topology

def firstWilsonBank {G : Gauge} (C : Family G) (L : Bulk.Chain C.path) (j p r : ℕ)
    (S : Scene C.path.levels p r) : Prop :=
    let P := L.kin.path (j+1) j
    let Q := L.kin.path (j+1) (j+1)
    let c := C.side j p
    let clip := (C.path.levels.params j).clip
    ∃ (B : Forest (C.path.levels.clock.op j p).ratio) (u : (C.path.levels.clock.op j p).Choices),
      let Z := colorCut B u Q (C.path.levels.params (j+1)).clip L.O (S.Poly (j+1))
        (L.kin.stationary (j+1) j p B)
      S.Poly j = bley (S.action j) Z (ink c clip P) ∧
      ∀ (I : Type) [DecidableEq I] [Fintype I] (R : Census I) (d : ℕ)
        (U : I → Stamp.Reservation C (C.side (j+1) p) d),
      ∀ (F : Forest (C.path.levels.clock.op j p).ratio) (v : (C.path.levels.clock.op j p).Choices)
        (x : Positions (Primary c G)) (i : ℕ), i ≤ r →
        let D := MSMatch.SourceTop.datum R j p U F v (tint G _ x)
        Lis.atlas Z r i P clip x =
          (D.vacuumAction L r i (tint G _ x)).re - (D.vacuumAction L r i 0).re

/-- One cutoff, independent of the volume and all tests, and one scene per
actual history. Its regular derivative envelope and calibrated reset cover
every retained scale, while its first non-bare coefficient bank is fixed
before the entire finite source family and every independent forest/tag. -/
def vacuumWilsonPrice {G : Gauge} (C : Family G) (L : Bulk.Chain C.path) (u : G.ColorIndex) : Prop :=
  ∀ (s p m q : ℕ), 6 ≤ s → 4 ≤ m → p+3 ≤ m → q+1 ≤ m → ∀ η : ℝ, 0 < η →
    ∀ᶠ k : ℕ in atTop, ∀ j n : ℕ, k ≤ j → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin (j+1) n k (p+1) (Lis.sun G u) S ∧
      (∀ i, k ≤ i → i ≤ j+1 →
        let Q := C.path.rep (j+1) n i
        let β := C.path.levels.clock.hatBeta i
        let w := Mosaic.vol β
        let g := Heath.Stock.cue Q.beta
        JetTab (Measuring.chart _ G) (Mosaic.αm β) s w (Metric.closedBall 0 w)
          (Aqua.film Q (S.Poly i) g p) q (g^((p:ℝ)+1-η))) ∧
      (∀ i, k ≤ i → i < j+1 →
        |Heath.Stock.cue (C.path.rep (j+1) n i).beta / Heath.Stock.cue (C.path.rep (j+1) n (i+1)).beta -
          Bakery.taste (p+1) (S.action i) (Heath.Stock.cue (C.path.rep (j+1) n i).beta)| ≤
          Mosaic.goalP (C.path.levels.clock.hatBeta i) (p+1)) ∧
      firstWilsonBank C L j n (p+1) S

theorem vacuumWilsonPrice_of_docket {G : Gauge} (hG : G.Simple) {C : Family G}
    (L : Bulk.Chain C.path) (physical : C.Makes) (stencils : ∀ d, Bid.pop (C.localSection d))
    (large : ∀ j n, Bid.Larger (G := G) (C.path.levels.clock.op j n)) (u : G.ColorIndex)
    (D : Docket C u L.O L.horizon L.kin) : vacuumWilsonPrice C L u := by
  intro s p m q hs hm hp hq η hη
  filter_upwards [calibrated_vacuum_envelope hG physical.wilson D s p m q hs hm hp hq hη] with k bought
  intro j n hj
  obtain ⟨S,hS,prices,reset⟩ := bought (j+1) n (hj.trans (Nat.le_succ j))
  exact ⟨S,hS,prices,reset,Wilson.first_vacuum_on_chain L physical stencils hS hj (large j n)⟩
end YM.Integration.FVA1Physical.Round2
