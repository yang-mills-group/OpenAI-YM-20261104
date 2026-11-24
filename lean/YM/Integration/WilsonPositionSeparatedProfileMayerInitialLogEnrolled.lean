import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogOriginal
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogPrescription

/-! Before the first physical cutoff, the full normalized logarithmic comparison of the
nominated initial marked Q with its independent compensated Wilson Taylor computation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogEnrolled
open Filter Function Finset Lattice Wilson RG Precision Tree Marker Multi Exterior
open FullQLocal FullQLocal.RenderedStep LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato
open Comparison.RG02 Comparison.RG02.Order Pert.Asymptotics WilsonLimitConstruction
open WilsonMatrixTicketLanesReportedPrepaid
open scoped Classical BigOperators Topology
variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
local notation "Γ" => Stock.census V

theorem original (R:Run G) (camp:Campaign R) (hG:G.Simple) (paid:Paid G R.kit) (u:V→MS.Rake.Label B)
    (Q:MS.Land.Prescription B) (cap K₀ q:ℕ) (μ:ℝ) {ε:ℝ} (ep:0<ε):
    ∃n ≥ q,∀ᶠ b:ℕ in atTop,∀(J:Request V),n ≤ J.order → ∀(A:NumericSchedule R.family J)
      (profile:∀k,k ≤ (R.metals.p.profile k).order ∧ k ≤ (R.metals.p.profile k).power)
      (d:LocalFormal.Datum R.family (Γ)),d.level=b→d.cutoff=d.level+1→
      ∀(o:V→Site (R.family.side (d.level+1) d.period)) (ks:V→ℕ),(∀i,ks i ≤ K₀)→
      ∀(hm:ActualOriginalQInitialInput.start R hG u J A profile ≤ d.level)
        (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val),
      ActualOriginalQLayout.referenceLevel R u ≤ d.level+1→
      ∀(t:TestSpace (ActualOriginalQPointSetup.request R u J).tests),
        let W:=(ActualOriginalQInitialInput.input R hG u J A d Q o μ ks profile hm hp).colors t
        let K:=d.kernel (RunFormalChain.fromRun R)
        let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
        let gₙ:=regulatorRun R.family (d.level+1) d.period (d.level+1)
        let S:=R.family.path.levels.clock.op d.level d.period
        let P:=R.family.path.rep d.cutoff d.period (d.level+1)
        let X:=((ActualOriginalQInitialPreparation.input R hG u J A d Q o μ ks).leaf t).density
        let w:=WilsonPositionSeparatedProfileMayerInitialLogWeights.weight
          (WilsonPositionSeparatedProfileMayerInitialThermalWords.reader R hG u J A d Q o μ ks t)
        ∀(F:Forest S.ratio)(tag:S.Choices)(a:fieldDir G (R.family.side d.level d.period) 1),
          (∀i,‖Exterior.collect G a i‖ ≤ (cap:ℝ)+1)→
          let Z:=fun _:S.Choices=>Integral.zone K P.p F g a
          Poly.price w (Local.markingError P X K g F tag W Z a n (Fintype.card V)) ≤ ε*gₙ^q:=by
  classical
  obtain ⟨n,grade,dates⟩:=WilsonPositionSeparatedProfileMayerInitialLogOriginal.original R hG paid u Q cap K₀ q μ ep
  refine ⟨n,grade,?_⟩
  filter_upwards [dates] with b sale
  intro J hired A profile d hb top o ks limits hm hp ref t W K g gₙ S P X w F tag a inside Z
  have receipt:=sale J A profile d hb top o ks limits hm hp ref t F tag a inside
  have cost:=WilsonPositionSeparatedProfileMayerInitialLogPrescription.funded R hG u J A d Q o μ ks
    profile hm hp camp top ref t F tag a n hired
  exact (congrArg (Poly.price w) cost).le.trans receipt.2.2

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogEnrolled
