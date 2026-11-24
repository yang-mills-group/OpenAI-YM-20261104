import YM.Integration.WilsonPhysicalStationMixedWickTest
import YM.Integration.WilsonMovingForkReporterBasisTariff

/-! Two original thermal stamps in one physical field can have different native grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterMixedBasis
open Lattice Wilson RG Source Cells Further.CorrectedLift
open Function Set Filter Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West
open Next.Rank.Atlas Next.Rank.Configuration Perch Glyph Marker Exponential Trace.Terrace
open PhysicalNext.RankCovariance PhysicalNext.InteractingRank MergeProof MergeProof.East Precision Bid Extra.Histories
open PhysicalNext PhysicalNext.InteractingRank.Soft RG.Supply Next.Rank.Station Marker Ac Corona Value Flux
open Next.Rank.Station Next.Rank.Tapes.West Market Next.Rank.Perch Tapes Peak
open Next.Rank.Glimmer Org Input MergeProof.Accent Extra.Histories PhysicalNext.Repeat.Legato.Bandage
open Next.Rank.Ribbon Vac.Numbers West Weaver Worker Radian
open WilsonOriginalBlissMixedGram (grades)
open WilsonMovingForkReporterRankMarket (amount)
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
open WilsonPhysicalStationThermalRanks (probe)
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G}

structure Slot (C:Family G) where
  left : ℕ
  right : ℕ
  dual : (C.labels.level right).Index
  turn : Signed
  arm : Fin 2
  site : Set (Points 2)
  compact : IsCompact site
  clear : site ⊆ conf 2

variable (v:Slot C)

def measured (x:(C.labels.level v.left).Index) :=
  WilsonPhysicalStationMixedWickTest.votes C (Pi.single x 1) (probe C v.dual v.turn v.arm)

def ordered (x:(C.labels.level v.left).Index):Prop :=
  ((C.labels.level v.left).grades x).2 ≤ ((C.labels.level v.right).grades v.dual).2

def ranked (x:(C.labels.level v.left).Index)(ok:ordered v x) :=
  WilsonPhysicalStationMixedWickTest.test C v.left v.right x v.dual v.turn v.arm ok v.site v.compact v.clear

def flat (x:(C.labels.level v.left).Index):ℝ :=
  max 0 (WilsonReporterWeightedMarket.compact (C:=C) (measured v x) v.compact v.clear).choose

private theorem graded (x:(C.labels.level v.left).Index)(ok:ordered v x){D:ℕ}
    (fit:∀i,(ranked v x ok).deg i≤D):
    ∀i,pure ((ranked v x ok).rank i) (thawKey (labels (ranked v x ok).raw fit i)) := by
  intro i
  fin_cases i
  · exact WilsonPhysicalThermalWickRankSupport.polynomial _ _ _ (WilsonPhysicalThermalWickRankSupport.axis _ x) (fit 0)
  · exact WilsonPhysicalThermalWickRankSupport.polynomial _ _ _ (WilsonPhysicalThermalWickProbe.original C v.dual v.turn v.arm) (fit 1)

variable {W:Bid.Worth}{u₀ ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}
    {door:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (B:Binding C)(H:C.Makes)(O:HaarBudget G)(J:ChartRatio G)
    (hg:G.Simple)(source:Scrim C W u₀ ψ φ δ (fly C.path.levels) r door)

def Posted {d:ℕ}(v:Slot C)(P:Tapes.Panel d)(k:ℕ)(z:ℝ):Prop :=
  ∀x:(C.labels.level v.left).Index,
    (∀ok:ordered v x, WilsonReporterWeightedRankEpoch.Result B H O J (u:=trays d) (K:=v.site)
      (measured v x) P (ranked v x ok).rank k (amount (ranked v x ok)) z) ∧
    WilsonReporterWeightedRankEpoch.Result B H O J (u:=trays d) (K:=v.site) (measured v x) P (fun _=>0) k (flat v x) z

include hg source
theorem sold (d θ:ℕ)(e z roof:ℝ)(active:100*(max v.left v.right+1)≤d)(shelf:d≤θ)
    (wide:(d:ℝ)+6≤roof)(tax:∀i≤d,generator G i≤z):
    ∀ᶠ k:ℕ in atTop,∀P:Tapes.Panel d,P.θ=θ→P.currency=e→P.arc≤roof→Posted B H O J v P k z := by
  classical
  have fit:∀i:Fin 2,grades v.left v.right i≤d := by
    have mx:max v.left v.right≤d:=by omega
    intro i
    fin_cases i
    · exact (le_max_left _ _).trans mx
    · exact (le_max_right _ _).trans mx
  have trade (x:(C.labels.level v.left).Index) :
      ∀ᶠ k:ℕ in atTop,∀P:Tapes.Panel d,P.θ=θ→P.currency=e→P.arc≤roof→
      (∀ok:ordered v x, WilsonReporterWeightedRankEpoch.Result B H O J (u:=trays d) (K:=v.site)
        (measured v x) P (ranked v x ok).rank k (amount (ranked v x ok)) z) ∧
      WilsonReporterWeightedRankEpoch.Result B H O J (u:=trays d) (K:=v.site) (measured v x) P (fun _=>0) k (flat v x) z := by
    have plain:=WilsonPhysicalStationThermalPlainInvoice.paid B H hg source O J (measured v x)
      θ e roof z tax (by exact Nat.le_add_left .. : 2≤trays d) fit v.compact v.clear (flat v x)
      (fun y hy=>((WilsonReporterWeightedMarket.compact (C:=C) (measured v x) v.compact v.clear).choose_spec y hy).2.trans (le_max_right ..))
    by_cases ok:ordered v x
    · have paid:=WilsonMovingForkReporterRankMarket.original B H hg source O J (ranked v x ok) d (trays d) θ e z roof
        active (active.trans shelf) (Nat.le_add_left ..) wide (fun i=>tax _ (fit i)) (graded v x ok fit)
      filter_upwards [plain,paid] with k unweighted weighted
      exact fun P ht he ha=>⟨fun _=>weighted P ht he ha,unweighted P ht he ha⟩
    · filter_upwards [plain] with k receipt
      exact fun P ht he ha=>⟨fun h=>(ok h).elim,receipt P ht he ha⟩
  filter_upwards [eventually_all.mpr trade] with k full
  exact fun P ht he ha x=>full x P ht he ha

theorem original (d:ℕ){n:ℕ}(menu:Fin n→Slot C)(z upper:ℝ)(wide:(d:ℝ)+6≤upper)
    (band:∀i≤d,generator G i≤z)(P:ℝ→Fin 3→Tapes.Panel d) :
    ∃k₀:ℕ,∀k≥k₀,∀j:Fin 3,∀s:Fin n,100*(max (menu s).left (menu s).right+1)≤d→
      ∀pan:Tapes.Panel d,pan.θ=(P 0 j).θ→pan.currency=(P 0 j).currency→pan.arc≤upper→Posted B H O J (menu s) pan k z := by
  let Live:={s:Fin n // 100*(max (menu s).left (menu s).right+1)≤d}
  have funded (j:Fin 3)(s:Live):=sold (menu s.1) B H O J hg source d (P 0 j).θ (P 0 j).currency z upper
    s.2 (P 0 j).enough wide band
  obtain ⟨k₀,go⟩:=eventually_atTop.mp (eventually_all.mpr (fun j=>eventually_all.mpr (funded j)))
  exact ⟨k₀,fun k hk j s good=>go k hk j ⟨s,good⟩⟩

end YM.Integration.WilsonMovingForkReporterMixedBasis
end
