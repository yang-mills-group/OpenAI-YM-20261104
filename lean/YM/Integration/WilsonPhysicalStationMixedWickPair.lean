import YM.Integration.WilsonPhysicalStationMixedWickTest
import YM.Integration.WilsonPhysicalStationThermalVotes
import YM.Integration.WilsonPhysicalStationThermalRanks
import YM.Integration.WilsonReporterWeightedRankEpoch
import YM.Integration.WilsonMovingForkReporterNamedInk

/-! Apply the paid original two-name experiment to the actual before-
cutoff reporter. Both duties belong to the same prior and named Vane. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPair
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open WilsonPhysicalStationMixedWickTest (votes reference)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationThermalPair (raw)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(B:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)
    {f:Extraction.Order}{S:(Bel R.family.book).Hierarchy}{h D u:ℕ}
    (V:Vane R.family h)(dl dr:Fin (h+1))(checked:V.checked f S h)
    {K:Set (Points 2)}{z bound:ℝ}(P:Tapes.Panel D)
local notation "AX"=>R.family.path.levels

def offered {N p:ℕ}(fine:V.k<N)(x:R.family.label dl)(y:(standard R.family).Field dr):
    (i:Fin 2)→R.family.label (grades dl dr i):=
  Fin.cons (α:=fun i=>R.family.label (grades dl dr i))
    (raw R V dl (p:=p) checked fine x) (fun _=>V.wheel.atCut (N,p) dr y)

def cell {N p:ℕ}(fine:V.k<N)(j:ℕ)(o:Fin 2 → Cover)(x:R.family.label dl)(y:(standard R.family).Field dr):ℂ:=
  R.family.numeric N p (q_asked (C:=R.family) (d:=grades dl dr) (offered R V dl dr (p:=p) checked fine x y))
    (fun i=>location R.family.S j N p (o i))

theorem original (x:R.family.label dl)(y:(standard R.family).Field dr)(q:Fin 2→ℕ)
    (ink:WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V u z)
    (bought:WilsonReporterWeightedRankEpoch.Result B R.makes O J (u:=u) (K:=K)
        (d:=grades dl dr) (votes R.family x y) P q V.k bound z):
    ∀ᶠ N:ℕ in atTop,∀ p:ℕ,∀ fine:V.k<N,∀ a:Points 2,
    tested AX V.b V.k a∈K → FitSky AX V.b V.k a →
      (R.family.path.levels.clock.monitor V.k)^(((q 1-q 0:ℕ):ℝ)+1/(16*u)) *
        ‖cell R V dl dr (p:=p) checked fine V.k (choose AX V.b V.k a) x y -
          reference R.family x y (tested AX V.b V.k a)‖≤bound:=by
  obtain ⟨l,r,L,unfolded⟩:=ink.bill
  have width:(P.bag (R.family.path.levels.clock.J V.k)).band=V.b:=(P.factor _).trans ink.aperture
  filter_upwards [bought] with N funded
  intro p fine a live fit
  obtain ⟨Ψ,act,stamps⟩:=unfolded N p fine
  obtain ⟨stL,sameL⟩:=stamps dl
  obtain ⟨stR,sameR⟩:=stamps dr
  let A:=(P.bag (R.family.path.levels.clock.J V.k))
  let Fₛ:=(Fin.cons (α:=fun i=>StampDuty R.family V.k N p (grades dl dr i) A.taylor Ψ A.era.coast.Q (PhysicalNext.RankCovariance.stamp R.family.path.levels N p)) stL (fun _=>stR))
  let v:=offered R V dl dr (p:=p) checked fine x y
  have solved (i:Fin 2):Price.Solves R.family (mag AX A.band V.k)
      (grades dl dr i) V.k N p (Fₛ i).T (votes R.family x y i) (v i):=by
    fin_cases i
    · change Price.Solves R.family (mag AX A.band V.k) dl V.k N p stL.T x (raw R V dl (p:=p) checked fine x)
      rw [show A.band=V.b from width,sameL]
      exact WilsonPhysicalStationThermalPair.solves R V dl checked fine x
    · change Price.Solves R.family (mag AX A.band V.k) dr V.k N p stR.T (Further.CorrectedLift.ladder R.family dr y) (V.wheel.atCut (N,p) dr y)
      rw [show A.band=V.b from width,sameR]
      have src:=WilsonPhysicalStationThermalPair.solves R V dr (p:=p) checked fine (Further.CorrectedLift.ladder R.family dr y)
      rwa [WilsonPhysicalStationThermalPair.lifted] at src
  have cash:=funded p fine l r L Ψ act a (width ▸ live) (width ▸ fit) Fₛ v solved
  rw [width,WilsonPhysicalStationMixedWickTest.reads] at cash
  exact cash

end YM.Integration.WilsonPhysicalStationMixedWickPair
end
