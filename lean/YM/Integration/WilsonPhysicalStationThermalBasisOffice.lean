import YM.Integration.WilsonPhysicalStationThermalPlainInvoice
import YM.Integration.WilsonMovingForkReporterRankMarket
import YM.Integration.WilsonMovingForkReporterFixedRanks

/-! Both prices depend on the actual finite named fields and compact
geometry. They are fixed before the angular horizon, thermal order,
aperture, date, original hierarchy of stamps and both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalBasisOffice
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft MergeProof
open Function Filter Set Lattice Wilson RG Labels Pressure Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open Source Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal Next.Rank.Ribbon MergeProof.Accent Extra.Histories PhysicalNext.Repeat.Legato.Bandage
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
open WilsonPhysicalThermalWickStretched (rates)
open WilsonReporterWeightedRankPrice (heats)
open scoped Topology BigOperators Classical
open WilsonPhysicalStationThermalRanks (probe fields)
open WilsonMovingForkReporterFixedRanks (Axes test portable)
open WilsonMovingForkReporterRankMarket (amount)
variable {G:Gauge} (C:Family G)(d:ℕ)
set_option quotPrecheck false
local notation "I"=>(C.labels.level d).Index
def rank (a:I):ℕ:=((C.labels.level d).grades a).2



def requested (b:I)(s:Signed)(side:Fin 2)(a:I):(i:Fin 2)→C.label d:=fields C (Pi.single a 1) (probe C b s side)

def axis (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)
    (b:I)(s:Signed)(side:Fin 2)(a:I)(ordered:rank C d a≤rank C d b):Axes C:=
    ⟨d,a,b,s,side,ordered,K,compact,clear⟩

def low (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)
    (b:I)(s:Signed)(side:Fin 2)(a:I):ℝ:=if h:rank C d a≤rank C d b then
    amount (test (axis C d K compact clear b s side a h)) else 0

def plain (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)
    (b:I)(s:Signed)(side:Fin 2)(a:I):ℝ:=max (WilsonReporterWeightedMarket.compact (C:=C)
    (requested C d b s side a) compact clear).choose 0

variable (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)

theorem plain_fee (b:I)(s:Signed)(side:Fin 2)(a:I)(v:Points 2)(hv:v∈K):
    Poly.price (fun _=>1) (Read.maxProfile C v (jointX (requested C d b s side a)))≤
      plain C d K compact clear b s side a:=
  ((WilsonReporterWeightedMarket.compact (C:=C) (requested C d b s side a) compact clear).choose_spec v hv).2.trans
    (le_max_left _ _)

variable {W:Bid.Worth}{u₀ ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}
    {door:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (B:Binding C)(H:C.Makes)(h:G.Simple)
    (source:Scrim C W u₀ ψ φ δ (fly C.path.levels) r door)
    (O:HaarBudget G)(J:ChartRatio G)

include h source
theorem original (b:I)(s:Signed)(side:Fin 2)(D u θ:ℕ)(e z roof:ℝ)(active:100*(d+1)≤D)(shelf:100*(d+1)≤θ)
    (two:2≤u)(wide:(D:ℝ)+6≤roof)(tax:∀i≤D,generator G i≤z):
    ∀ᶠ k:ℕ in atTop,∀pan:Tapes.Panel D,pan.θ=θ→pan.currency=e→pan.arc≤roof→
      ∀a:I,
      (rank C d a≤rank C d b→WilsonReporterWeightedRankEpoch.Result B H O J (u:=u) (K:=K)
          (requested C d b s side a) pan ![rank C d a,rank C d b] k (low C d K compact clear b s side a) z) ∧
      WilsonReporterWeightedRankEpoch.Result B H O J (u:=u) (K:=K)
          (requested C d b s side a) pan (fun _=>0) k (plain C d K compact clear b s side a) z:=by
  classical
  have mono:d≤D:=by omega
  have pay (a:I):∀ᶠ k:ℕ in atTop,∀pan:Tapes.Panel D,pan.θ=θ→pan.currency=e→pan.arc≤roof→
      (rank C d a≤rank C d b→WilsonReporterWeightedRankEpoch.Result B H O J (u:=u) (K:=K)
          (requested C d b s side a) pan ![rank C d a,rank C d b] k (low C d K compact clear b s side a) z) ∧
      WilsonReporterWeightedRankEpoch.Result B H O J (u:=u) (K:=K)
          (requested C d b s side a) pan (fun _=>0) k (plain C d K compact clear b s side a) z:=by
    have basic:=WilsonPhysicalStationThermalPlainInvoice.paid B H h source O J (requested C d b s side a)
        θ e roof z tax two (fun _=>mono) compact clear (plain C d K compact clear b s side a)
        (plain_fee C d K compact clear b s side a)
    by_cases under:rank C d a≤rank C d b
    · let A:=axis C d K compact clear b s side a under
      have posted:=WilsonMovingForkReporterRankMarket.original B H h source O J (test A) D u θ e z roof active shelf two
          wide (fun _=>tax _ mono) (portable A mono)
      filter_upwards [basic,posted] with k base signed
      intro pan th ec fit
      refine ⟨fun _=>?_,base pan th ec fit⟩
      rw [low,dif_pos under]
      exact signed pan th ec fit
    · filter_upwards [basic] with k base
      exact fun pan th ec fit=>⟨fun impossible=>(under impossible).elim,base pan th ec fit⟩
  filter_upwards [Filter.eventually_all.mpr pay] with k all
  exact fun pan th ec fit a=>all a pan th ec fit

end YM.Integration.WilsonPhysicalStationThermalBasisOffice
end
