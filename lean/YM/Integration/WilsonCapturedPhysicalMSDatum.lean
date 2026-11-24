import YM.FVA2.Main
namespace YM.Integration.WilsonCapturedPhysicalMSDatum
open MS MS.Land FVA2 FVA2.Register
noncomputable def original (G : Gauge) : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)) :=
  Classical.choice (bookedMS (Position.OpenAxis.Plot (Press.portDeck G)))
theorem matched {G : Gauge} (N : WilsonPrescription G) (h : G.Simple) (dial : Bool) :
    ∃ S, Main.Match N h (original G) S dial :=
  Main.wilson_to_MS N h (original G) dial
end YM.Integration.WilsonCapturedPhysicalMSDatum
