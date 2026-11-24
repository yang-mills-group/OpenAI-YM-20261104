import YM.Integration.WilsonMacroscopicRichMSCoefficient

/-! Evaluate each signed independent MS OPE coefficient with the very same detector used on the original cutoff law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichMSProbe
open Function Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.O FVA2.ColorCode RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open FVA2.Scale Extraction Table Spec Climb PhysicalNext.Repeat.Legato PhysMS
open Wilson Lattice
open Trace.Physical.GermGraph Trace.Physical RG16 RG16.Literal Analysis
open Push.Local Source Labels ProjectorNext.Equivariance RGComparison.Core16
open WilsonMacroscopicRichCapturedProbes WilsonMacroscopicRichCapturePropagation
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){S:Table R.family.book}
local notation "B₀" => Press.portDeck G

def read {h u N p:ℕ}(J:ℝ→tower S)(r:ℝ)(door:Opened R.family h u p)(uN:u≤N)(probe:Probe G h):
    (Bel R.family.book).Field h→ₗ[ℂ]ℂ:=
  (runProbe (R.family.labels.level h) probe).toLinearMap.comp
    ((fitting h N p u R.makes door uN).toLinearMap.comp
      ((R.family.factory h N p).terminal.symm.toLinearMap.comp ((S.representative h).comp (J r h).toLinearMap)))

theorem original {n h u N p:ℕ}(M:MS_Data G (Position.OpenAxis.Plot B₀))(J:ℝ→tower S)(r:ℝ)
    (door:Opened R.family h u p)(uN:u≤N)(t:Probe G h)(d:Fin n→ℕ)(v:(i:Fin n)→(Bel R.family.book).Field (d i))
    (μ:ℝ)(x:Points n)(γ:ℝ)(q:ℕ):
    runProbe (R.family.labels.level h) t (forecast R door uN (S.representative h
      (J r h (WilsonMacroscopicRichMSCoefficient.field R M h d v μ x γ q))))=
      ∑b:Glyph B₀ h,WilsonMacroscopicRichMSCoefficient.coefficient R M d v μ x γ q b*
        read R J r door uN t ((exactField R.family.labels h).symm ((Daylight B₀ h) b)):=by
  change read R J r door uN t (WilsonMacroscopicRichMSCoefficient.field R M h d v μ x γ q)=_
  simp only [WilsonMacroscopicRichMSCoefficient.field,map_sum,map_smul,smul_eq_mul]

theorem observed {n h u b N p:ℕ}(M:MS_Data G (Position.OpenAxis.Plot B₀))(J:ℝ→tower S)(r:ℝ)
    (P:Finset (Probe G h))(door:Opened R.family h u p)(ub:u≤b)(uN:u≤N)(Z:Config G (R.family.side b p)→ℂ)
    (d:Fin n→ℕ)(v:(i:Fin n)→(Bel R.family.book).Field (d i))(μ:ℝ)(x:Points n)(γ:ℝ)(q:ℕ):
    WilsonMacroscopicRichIndependentHearing.debit R P door ub uN (S.representative h
      (J r h (WilsonMacroscopicRichMSCoefficient.field R M h d v μ x γ q))) Z=
      ∑t∈P,‖(∑a:Glyph B₀ h,WilsonMacroscopicRichMSCoefficient.coefficient R M d v μ x γ q a*
        read R J r door uN t ((exactField R.family.labels h).symm ((Daylight B₀ h) a)))-
        Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z)‖:=by
  unfold WilsonMacroscopicRichIndependentHearing.debit
  simp only [original]

end YM.Integration.WilsonMacroscopicRichMSProbe
