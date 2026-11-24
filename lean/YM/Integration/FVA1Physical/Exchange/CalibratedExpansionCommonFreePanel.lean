import YM.FVA2.XReg.Continuum
import YM.WilsonMS.Scales.Carried

namespace YM.Integration.FVA1Physical.Exchange.CalibratedExpansion

open MS.Land XSpace.Normalize

variable {G : Gauge} {O : Booked (FVA2.Press.portDeck G)}
  {M : Booked (WilsonMS.Ensure.deck G)} (T : MS_Data G O) (F : MS_Data G M)
  (ν μ : ℝ) (d : ℕ)

theorem original_free_reports :
    FVA2.Reg.CoverTest.Rates ν T d 0 = WilsonMS.VisitH.Continuum F μ 0 d :=
  (FVA2.Reg.CoverTest.ground (d := d) ν T).trans (WilsonMS.VisitH.free_match F μ d).symm

theorem original_free_panel (V : Store G) :
    (V.measure d).D (FVA2.Reg.CoverTest.Rates ν T d 0) =
      (V.measure d).D (WilsonMS.VisitH.Continuum F μ 0 d) :=
  congrArg (V.measure d).D (original_free_reports T F ν μ d)

theorem original_free_separated_read {n : ℕ} {x : Points n} (hx : x ∈ conf n)
    (v : XSpace.Structure1.Tags G d n) :
    FVA2.Dframe.meteor ν T d x 0 v = WilsonMS.VisitH.lowKernel F μ 0 d x v :=
  (congrArg (fun a : XSpace.Structure1.Point G d n => a v)
    (FVA2.Dframe.limit_lead (d := d) ν T hx)).trans
    (WilsonMS.VisitH.leadingPoint F μ hx v).symm

theorem original_free_fit_origins (V : Store G) :
    FVA2.Reg.State.root ν V T d 0 = WilsonMS.FrameConj.Gates.Lμ V F μ d 0 :=
  (FVA2.Reg.State.baseK (d := d) ν V T).trans (WilsonMS.GFlow.KnotBase F V μ d).symm

end YM.Integration.FVA1Physical.Exchange.CalibratedExpansion
