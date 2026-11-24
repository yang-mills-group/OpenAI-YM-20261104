import YM.Integration.WilsonPhysicalStationMixedBasisSale
/-! Signed whole-field heat balance with a previously elected lower at every original cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedMeasuredTicket
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical

open WilsonMovingForkReporterRankCourse (surplus)
open WilsonMovingForkReporterMixedBasis (Slot Posted ordered ranked flat measured)
open WilsonMovingForkReporterRankMarket (amount)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationMixedWickTest (votes reference)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonOriginalBlissMixedGram (grades)
open scoped Classical BigOperators Topology
open WilsonPhysicalStationMixedBasisSale (fee Sold)
open WilsonPhysicalStationMixedBilledPort (base)
open WilsonPhysicalStationMixedListener (value)
open WilsonPhysicalStationMeasuredCash (aperture)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMixedChartCharge (wage)
open WilsonPhysicalStationThermalStart (entered)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D D' e depth:ℕ}(A:Vane R.family D)(B:Vane R.family D')(v:Slot R.family)
    (da:v.left<D+1)(db:v.left<D'+1)(dr:v.right<D+1)(ca:A.checked f H D)(cb:B.checked f H D')
local notation "d₀"=>(⟨v.left,da⟩:Fin (D+1))
local notation "d₁"=>(⟨v.left,db⟩:Fin (D'+1))
local notation "d₂"=>(⟨v.right,dr⟩:Fin (D+1))
local notation "AX"=>R.family.path.levels
local notation "t₀"=>(AX).clock.monitor A.k
local notation "M₀"=>Station.mag (AX) A.b A.k
local notation "M₁"=>Station.mag (AX) B.b B.k
local notation "l₀"=>R.family.labels.level v.left
local notation "z₀"=>probe R.family v.dual v.turn v.arm
local notation "q₂"=>rank R.family v.right v.dual

def capital:ℝ:=∑a,|fee R v a|
def rate (depth:ℕ):ℝ:=capital R v/((depth:ℝ)+1)
lemma paid (depth:ℕ):0≤rate R v depth:=
  div_nonneg (Finset.sum_nonneg (fun _ _=>abs_nonneg _)) (by positivity)

def Reads (e depth:ℕ):Prop:=
  ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k<N,∀a:(l₀).Index,∀w:R.family.label v.left,
    (if B.k=A.k then WilsonPhysicalStationCoincidentLower.Receipt R A B v.left e da db (p:=p) ca cb top a w
      else WilsonPhysicalStationSelectedLower.Receipt R A B v.left e da db (p:=p) ca cb top a w)→
    ∀x:Points 2,tested AX A.b A.k x∈v.site→FitSky AX A.b A.k x→
      let q:=rank R.family v.left a
      let ξ:=tested AX A.b A.k x
      let Z:=entered R B (d₁) (p:=p) cb top (Pi.single a 1)-(R.family.factory v.left N p).terminal w
      let χ:ℂ:=signal R N p A.k B.k v.left q (M₀) (M₁)
      ‖WilsonPhysicalStationMixedListener.value R N p A.k (choose AX A.b A.k x) Z (A.wheel.atCut (N,p) (d₂) (z₀))-χ*base R v.left (z₀) ξ a‖*(t₀)^(q₂)
        ≤wage R q (q₂) (rate R v depth) (∑i,‖base R v.left (z₀) ξ i‖) A.k v.left*(t₀)^q

theorem original (dates:B.k=A.k ∨ B.k=A.k+1)(warm:WilsonPhysicalStationBasisClock.Live R A.k)
    (window:aperture R A.k B.k v.left (M₀) (M₁)≤1)(sold:Sold R A v da dr depth ca):
    Reads R A B v da db dr ca cb e depth:=by
  classical
  filter_upwards [sold] with N heard
  intro p top a w stamped x inside fit
  let ξ:=tested AX A.b A.k x
  let z:=probe R.family v.dual v.turn v.arm
  let Γ:=base R v.left z ξ
  let ψ:=fun i=>(cell R A (d₀) (d₂) (p:=p) ca (show A.k<N by omega) A.k (choose AX A.b A.k x) (Pi.single i 1) z)
  have bill (i:(l₀).Index):
      ((depth:ℝ)+1)*(t₀)^(((q₂)-rank R.family v.left i:ℕ):ℝ)*‖ψ i-Γ i‖≤capital R v:=
    (heard p (show A.k<N by omega) x inside fit i).trans ((le_abs_self _).trans
       (Finset.single_le_sum (f:=fun t=>|fee R v t|) (fun _ _=>abs_nonneg _) (Finset.mem_univ i)))
  apply WilsonPhysicalStationMixedBilledPort.original R A B da db ca cb dates top warm window a w stamped dr
    v.dual v.turn v.arm A.k (choose AX A.b A.k x) ξ (rate R v depth) (paid R v depth)
  · intro i small
    change ‖ψ i-Γ i‖*(t₀)^(q₂)≤rate R v depth*(t₀)^(rank R.family v.left i)
    have temp:0≤(t₀):=(Real.exp_pos _).le
    have refund:=WilsonPhysicalStationBasisIncome.graded temp (show rank R.family v.left i≤(q₂) from small) (bill i)
    simpa only [neg_zero,Real.rpow_zero,mul_one,rate] using refund
  · intro i large
    change ‖ψ i-Γ i‖≤capital R v/((depth:ℝ)+1)
    apply (le_div_iff₀ (by positivity : 0<(depth:ℝ)+1)).2
    have invoice:=bill i
    have order:(q₂)≤rank R.family v.left i:=large.le
    rw [Nat.sub_eq_zero_of_le order,Nat.cast_zero,Real.rpow_zero,mul_one] at invoice
    exact (mul_comm _ _).trans_le invoice

theorem funded (bind:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)
    (P:Tapes.Panel depth){z:ℝ}(ink:WilsonMovingForkReporterNamedInk.Filed bind R.makes O J P A (MergeProof.East.trays depth) z)
    (ripe:(depth:ℝ)+1 ≤(AX).clock.monitor A.k^(surplus depth))(posted:Posted bind R.makes O J v P A.k z)
    (dates:B.k=A.k ∨ B.k=A.k+1)(warm:WilsonPhysicalStationBasisClock.Live R A.k)
    (window:aperture R A.k B.k v.left (M₀) (M₁)≤1):
    Reads R A B v da db dr ca cb e depth:=
  original R A B v da db dr ca cb dates warm window
    (WilsonPhysicalStationMixedBasisSale.original R bind O J A v da dr ca P ink ripe posted)

end YM.Integration.WilsonPhysicalStationMixedMeasuredTicket
end
