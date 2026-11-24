import YM.Integration.WilsonPhysicalExteriorPeriodPair
import YM.Integration.WilsonEpochPostedComparison
import YM.Integration.WilsonPositionProgramPrescription
import YM.Integration.WilsonWindowFormalAnnouncement
import YM.Integration.WilsonWindowReportingRun

/-! The two finite periods on the actual funded run, with the original
independent data and exactly the historically prescribed bulk program. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFundedPeriod
open Function Set Filter Real Lattice Precision RG PhysicalNext.Repeat.Legato RegulatorIR RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Moving Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping
open MS MS.Land MS.Menus MS.Rake MS.Dial MS.Vista MS.Fleet MS.Orbit MS.Tide MS.Tone
open FVA2 FVA2.Register YM.FVAAlt2 FormalOPE
open WilsonPhysicalExteriorResolvedReadout WilsonPhysicalExteriorResolvedCutoff WilsonPhysicalExteriorUVStory
open scoped Topology BigOperators Classical

variable {G:Gauge} (C:Run G)
local notation "Y₀" => Oracle.books C.family.path.levels.clock.kernel
local notation "B₀" => FVA2.Press.portDeck G
local notation "M₀" => MS_Data G (FVA2.Position.OpenAxis.Plot B₀)

def Periods (Z:∀ b:Patch,b.Branches C.family.path.levels.clock.kernel G)
    (R:Lodge.Contract C Y₀ Z) (τ:Prescription B₀) : Prop :=
  ∀ (p:ℕ) (g:G.ColorIndex) (t:ℕ→ℕ) (ht:∀i,R.floor Y₀ Z C≤t i)
    (_:Tendsto t atTop atTop) (_:∀i,p≤t i),
    let track:=WilsonPhysicalExteriorRegulator.nativeTrack Y₀ Z C R t ht
    let stages:=Period.Field.LodgeT.instance_real Y₀ Z C R t ht
    ∃ F:Calibration.Tent track.entire,
      Calibration.Notebook track.desk Y₀ G Z g (Rocket.native track.entire) F p ∧
      track.VenueT track.origin ∧
      ∀ (n h:ℕ) (k₀:ℕ→ℕ) (r E:ℕ→ℝ) (_:∀i,0<E i),
      let Λ:=fun i=>RG16.Lambda C.family.path.levels (k₀ i)
      ∃ σ:ℕ→ℕ, ∃ A:ℝ,0≤A ∧ ∃ b:ℕ,
      ∀ (μ:ℝ) (W:Fin n→ℕ→ Cover) (D:Fin n→Sound.Ethos.MenuF B₀ h)
        (k:ℕ), k≤p →
        Reach (track.PoseT μ track.origin W).profile W →
        Resolved (track.PoseT μ track.origin W).profile (info W) →
        (∀ i j,‖Tone.embed (track.origin i+W j i)‖≤r i) → Tendsto Λ atTop atTop →
        ∀ {d c:ℝ},c<2 → (∀ᶠ i:ℕ in atTop,track.Θ i≤d*(Λ i)^c) →
        ∃ P:ℝ,0<P ∧ ∀ᶠ i:ℕ in atTop,∀ q,σ i≤q →
          ‖PowerSeries.coeff k (Sound.Figure.runPer C Z stages (fun i j=>track.origin i+W j i)
            (Calibration.sheet F) q track.stop (Sound.Ethos.owner∘D) τ (μ-track.Θ i)
            (Sound.Alone track i) i) -
           WilsonPhysicalExteriorPeriodPair.bank Y₀ Z C R t ht τ μ track.origin W Λ
             (Sound.Ethos.owner∘D) k i‖ ≤
           A*(1+|μ|)^b*E i+P*exp (-mildG*track.Θ i)

theorem on_run {hG:G.Simple} (N:WilsonPrescription G) {M:M₀} {S:Prescription B₀}
    {dial:Bool} (matchMS:Main.Match N hG M S dial)
    (purchase:NativeFVAPlateau.Correlations C) :
    ∃ (Z:∀ b:Patch,b.Branches C.family.path.levels.clock.kernel G)
      (R:Lodge.Contract C Y₀ Z) (τ:Prescription B₀),
      τ.team=S.team ∧ TaylorOKPl M (Lobby.Table (basisR C) B₀) τ ∧ Periods C Z R τ := by
  obtain ⟨Z,R,_,_,_,_⟩:=purchase
  obtain ⟨τ,eq,ok⟩:=WilsonPhysicalExteriorHistoricPrescription.booked C N matchMS
  refine ⟨Z,R,τ,eq,ok,?_⟩
  intro p g t ht growing order
  let track:=WilsonPhysicalExteriorRegulator.nativeTrack Y₀ Z C R t ht
  obtain ⟨F,notebook⟩:=Calibration.tomorrows track.desk Y₀ G Z g (Rocket.native track.entire) p
  refine ⟨F,notebook,track.visible,?_⟩
  intro n h k₀ r E positive
  obtain ⟨σ,A,hA,b,price⟩:=WilsonPhysicalExteriorPeriodPair.finite (n:=n) Y₀ Z C R t ht F M τ
    notebook hG growing order ok r E positive h
  refine ⟨σ,A,hA,b,?_⟩
  intro μ W D k hk reach sep radius grow d c hc cmp
  exact price μ track.origin W D k hk track.visible reach sep radius _ grow hc cmp

end YM.Integration.WilsonPhysicalExteriorFundedPeriod
end
