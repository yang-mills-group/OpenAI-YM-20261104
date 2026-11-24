import YM.Integration.WilsonPhysicalStationWeightedAxis
import YM.Integration.WilsonPhysicalStationResidualWallet
import YM.Integration.WilsonPhysicalStationDetectorCurrency

/-! Directed physical original-vacuum scalar of a nominated input and detector
after compensating the actual lower engineering plane at both dates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationObservedEntry
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFineCorrection (measured)
open WilsonPhysicalStationRegisteredDiagonal (ratio ceiling)
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationEndCurrency (row charge)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationWeightedAxis (purse)
open WilsonPhysicalStationThermalPair (cell)
open WilsonPhysicalStationTableJump (pair)
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West Rise Alarm Paint Next.Rank.Station Glimmer
open Ward MergeProof.Accent Next.Rank.Ribbon
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {f:Extraction.Order} {S:Table R.family.book}
  (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
  {D D':ℕ} (A:Vane R.family D) (B:Vane R.family D') {N p:ℕ}
  (h e:ℕ) (da:h  <  D+1) (db:h  <  D'+1)
local notation "a₀" => (⟨h,da⟩:Fin (D+1))
local notation "b₀" => (⟨h,db⟩:Fin (D'+1))
local notation "L₀" => R.family.path.levels
local notation "F₀" => R.family.labels.level h
local notation "μ" => (F₀).coeffSize
local notation "P₀" => Columns.low (F₀) e
local notation "K₀" => R.family.factory h N p
local notation "C₀" => ((L₀).params A.k).columns
local notation "C₁" => ((L₀).params B.k).columns
local notation "δ₀" => barunit (R.family.S.block A.k)
local notation "D₀" => (F₀).scaled (ratio R A.k)

local notation "M₀" => Station.mag (L₀) A.b A.k
local notation "M₁" => Station.mag (L₀) B.b B.k


local notation "t₀" => (shrink R.family A.k N p)⁻¹
local notation "t₁" => (shrink R.family B.k N p)⁻¹


def born (h:ℕ) (geometry:Points 2) (z:(standard R.family).Field h)
    (i:(R.family.labels.level h).Index):ℂ:=
  (standard R.family).classMoment (standard R.family) (fun _:Fin 2=>h) geometry
     ![(standard R.family).project h (Pi.single i 1),z]

local notation "T₀" => (L₀).clock.monitor A.k

include L fac in
theorem original (hg:G.Simple) (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k+1) (top:B.k < N) (horizon:h=e+1)
    (gate:(C₀)*err R A.k ≤ 1/2) (a:(F₀).Index) (weight:((F₀).grades a).1=h)
    (x:Points 2) (z:(standard R.family).Field h) (Q:ℕ)
    (J κ:ℝ) (bill:0 ≤ J)(large:4 ≤ T₀)(small:κ ≤ 1/2)
    (low:∀i, ((F₀).grades i).2 ≤ Q →
       ‖cell R A (a₀) (p:=p) ca (show A.k < N by omega) A.k (choose (L₀) A.b A.k x) (Pi.single i 1) z-
           born R h (tested (L₀) A.b A.k x) z i‖*(T₀)^Q  ≤  J*(T₀)^((F₀).grades i).2*(T₀)^(-κ))
    (high:∀i, Q < ((F₀).grades i).2 →
       ‖cell R A (a₀) (p:=p) ca (show A.k < N by omega) A.k (choose (L₀) A.b A.k x) (Pi.single i 1) z-
           born R h (tested (L₀) A.b A.k x) z i‖ ≤ J)
    (off:∀i, ((F₀).grades i).2≠Q→born R h (tested (L₀) A.b A.k x) z i=0):
    let s:R.family.label h:=Pi.single a 1
    let y:=entered R B (b₀) (p:=p) cb top s
    let q:=((F₀).grades a).2
    let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
    let Γ:=born R h (tested (L₀) A.b A.k x) z
    let ρ:=rate R A.k B.k h
    ∃ W:R.family.label h,(P₀) W=W ∧ (P₀) (A.R N p (a₀) (y-(K₀).terminal W))=0 ∧
      (∀i:(F₀).Index,(1-err R B.k)*‖filed R A (a₀) N p (y-(K₀).terminal W) i-χ*s i‖*(t₀)^((F₀).grades i).2 ≤
        ρ*purse R N p A.k B.k h q (M₀) (M₁)) ∧
      (1-err R B.k)*‖WilsonPhysicalStationTableJump.pair R (a₀) N p A.k (choose (L₀) A.b A.k x) (y-(K₀).terminal W)
        (A.wheel.atCut (N,p) (a₀) z)-χ*Γ a‖*(t₀)^Q  ≤ 
        purse R N p A.k B.k h q (M₀) (M₁)*
          (J*4^Q*(T₀)^(-κ)*((ratio R A.k)^q+Fintype.card (F₀).Index*ρ)+ρ*∑ i,‖Γ i‖):=by
  intro s y q χ Γ ρ
  have live:A.k < N:=by omega
  obtain ⟨W,lower,gone,payment⟩:=WilsonPhysicalStationWeightedAxis.original R L fac A B h e da db
    (p:=p) hg ca cb dates top horizon gate a weight
  refine ⟨W,lower,gone,payment,?_⟩
  let Z:=y-(K₀).terminal W
  let c:=filed R A (a₀) N p Z
  let site:=choose (L₀) A.b A.k x
  let moment:=WilsonPhysicalStationTableJump.pair R (a₀) N p A.k site Z (A.wheel.atCut (N,p) (a₀) z)
  obtain ⟨pos,minP,maxP⟩:=WilsonPhysicalStationDetectorCurrency.original R p live.le
  obtain ⟨safe,enough,room⟩:=WilsonPhysicalStationDetectorCurrency.reserve large maxP small
  have price:0 ≤ J*4^Q:=by positivity
  have above:J ≤ J*4^Q:=le_mul_of_one_le_right bill (one_le_pow₀ (by norm_num))
  have table:=WilsonPhysicalStationDirectedRead.original R A (a₀) (p:=p) ca live A.k site z Z Γ Q
    ((T₀)^(-κ)) (J*4^Q) safe enough price room
    (fun i hi=>WilsonPhysicalStationDetectorCurrency.low hi (Real.exp_pos _).le pos.le bill enough
      (norm_nonneg _) minP maxP (low i hi)) (fun i hi=>(high i hi).trans above)
  have debit:=WilsonPhysicalStationThermalCoordinates.original R A (a₀) (p:=p) live Z
  change (∑ i,‖c i‖*(t₀)^((F₀).grades i).2)=WilsonPhysicalStationHorizontalWallet.normAt (F₀) (M₀)⁻¹ (A.R N p (a₀) Z) at debit
  have money:‖moment-∑ i,c i*Γ i‖*(t₀)^Q  ≤  J*4^Q*(T₀)^(-κ)*(∑ i,‖c i‖*(t₀)^((F₀).grades i).2):=by
    apply table.trans_eq
    rw [debit]
    ring
  exact WilsonPhysicalStationResidualWallet.original (fun i=>( (F₀).grades i).2) a c Γ χ moment Q
    (WilsonPhysicalStationFiledGate.refund R B) pos.le enough price
    (WilsonPhysicalStationWeightedAxis.principal R A B h da (p:=p) dates top q) payment money off

end YM.Integration.WilsonPhysicalStationObservedEntry
end
