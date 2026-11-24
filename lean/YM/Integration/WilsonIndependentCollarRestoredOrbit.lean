import YM.Integration.WilsonIndependentCollarStationPayment
import YM.Integration.WilsonOriginalCensusRosterFare

/-! Restore the true finite canonical columns on the actual two orbital tables
using their signed sum of wages, before the UV cutoff or period. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarRestoredOrbit
open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior Next.Foundations
open Work.F08 WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonMarkedIndependentPhysicalIntake WilsonMarkedIndependentMixedGeometry
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open PhysicalNext.Repeat.Legato Marker Multi QuadraticLocal QuadraticLocal.Earn
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open WilsonReceivedDepositedOrbitalFixedMoments (program)
open WilsonOriginalCensusRosterMenu (sheets central Paid)
open WilsonOriginalCensusRosterFare (whole)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open WilsonIndependentCollarOriginalDose (axisFee)
open WilsonIndependentCollarOrbitalBasisPayment (Choices)
open WilsonIndependentCollarPaidWindingPanel (signed)
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonOriginalSparseFiledOpening (near)
open scoped Classical BigOperators Topology

variable {G:Gauge}{n q:ℕ}{D k:Fin n→ℕ}{I:Type}[Fintype I][DecidableEq I]

def letter (R:Run G)(T:Finset (Fin n))(s:Choices R k T)(v:Fin n):Choice R k v:=
  if h:v∈T then s ⟨v,h⟩ else .inl ()

theorem occupied (R:Run G)(T:Finset (Fin n))(s:Choices R k T)(v:T):
    letter R T s v=s v:=by simp [letter,v.property]

def ceiling (k:Fin n→ℕ)(words:I→Finset (Fin n))(p:ℕ):ℕ:=(∑i:I,mass k (words i))+p

omit [DecidableEq I] in
theorem fits {a p:ℕ}(words:I→Finset (Fin n))(active:Finset I)(rank:a≤p):
    mass (fun i=>mass k (words i)) active+a≤ceiling k words p:=
  Nat.add_le_add (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)) rank

def reading (R:Run G)(κ:(j:Fin n)→Knob (D j))(pt:Fin n→Chamber)(N K i q a:ℕ)
    (sites:Fin n→ Cover)(t:Case D)(cells:Digits R.family.path.levels (Fin n))(front:I→Fin n)
    (grid:Side)(digit:I→Site (loose R.family.path.levels i).L)
    (place:(J:Finset I)→J→I→ Cover)(Z:Stationary.Link G grid)
    {side:Side}{P:Passport side (Fin n)}(B:I→Binder P (Stock.census (Fin n)))
    (x:Affinity.Wallet (room (Fin n)))(target:(Stock.census (Fin n)).Mode)(head:∀J:Finset I,J.Nonempty→J)
    (seed:Choices R k target.val)(repeated:Bool):ℂ:=
  let words:=fun i:I=>(B i).mode.val
  let ranks:=fun i=>mass k (words i)
  let old:=program (k:=k) (fixed R k κ pt N K (i+1) cells (letter R target.val seed))
    q words front (fun _=>sites) (fun _=>t)
  if repeated then
    limUnder (coverFilter R.family.path.levels.S i grid) (fun u=>∑s:Finset I,wages B x target s*
      whole ranks a s head (fun J o r=>sheets R ranks N i q grid old digit J o.val (place J o) a r Z u))
  else ∑s:Finset I,wages B x target s*whole ranks a s head
    (fun J o r=>central R ranks N i q grid old digit J o.val (place J o) a r Z)

/-- The measured station, Taylor order and finite footprint are chosen before
the physical period. Both numerical tables retain all the actual occupied roots. -/
theorem original (R:Run G)(κ:(j:Fin n)→Knob (D j))(pt:Fin n→Chamber)(simple:G.Simple)
    (quiet:WilsonReceivedCloseFundedHeat.Quiet R)(salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (words:I→Finset (Fin n))(front:I→Fin n)(named:∀i,front i∈words i)
    (C:Fin n→ℝ)(capC:∀i,0≤C i)(A:ℕ):
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀(K i:ℕ),m ≤ i → i < K →
      L.S.scale K-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀(Q:Realm G (q+1) Credit.leanC),Q.anchor ≤ i → Q.draws=L → Q.paid=R.metals.O →
      ∀(target:(Stock.census (Fin n)).Mode)(M:Fin n→ℝ)(p power pole E diameter:ℕ),p≤q →
      let H:=R.alloy.B.a.clock.hatBeta (i+1)
      0 < H →
      ∀ᶠ per:ℕ in atTop,∀N,K≤N →
      ∀(v:(j:Fin n)→R.family.label (k j)),(∀j∈target.val,axisFee R k v j≤M j) →
      ∀(side:Side)(P:Passport side (Fin n))(B:I→Binder P (Stock.census (Fin n))), (fun i=>(B i).mode.val)=words →
      ∀(x:Choices R k target.val→Affinity.Wallet (room (Fin n)))(t:Choices R k target.val→Case D),
        (∀a j,‖t a j‖≤C j) → ∀(cells:Digits L (Fin n))(sites:Fin n→ Cover)
      (grid:Side), (R.family.side i per).val∣grid.val →
      ∀(digit:I→Site (loose L i).L)(place:(J:Finset I)→J→I→ Cover),
        (∀J:Finset I,∀o:J,breadth J o.val 0 (relative J o.val (place J o))≤diameter) →
      ∀(Z:Stationary.Link G grid),‖Z‖≤1 → ∀(head:∀J:Finset I,J.Nonempty→J)(r d:ℕ),r≤p → d≤r →
      let value:=fun seed=>reading R κ pt N K i q d sites (t seed) cells front grid digit place Z B (x seed) target head seed
      ‖(∑s,signed R k N per K m v target.val s * value s true)-
        (∑s,signed R k N per K m v target.val s * value s false)‖ ≤ (H^(near power pole E))⁻¹:=by
  intro L
  obtain ⟨_,_,cash⟩:=WilsonIndependentCollarStationPayment.original (I:=I) R simple k A
  obtain ⟨floor,menu⟩:=eventually_atTop.mp (WilsonOriginalCensusRosterMenu.original (k:=k) (e:=q)
    R κ pt simple quiet salary bought words front named C capC)
  filter_upwards [cash,eventually_ge_atTop floor] with m pay late
  intro K i lower upper span Q anchor draw book target M p power pole E diameter pq H hot
  obtain ⟨ε,pos,_,restore⟩:=pay K i (lower.trans upper.le) span target M p power pole E hot
  let limit:=ceiling k words p
  let δ:=ε/((limit:ℝ)+1)
  have factor:0<(limit:ℝ)+1:=by positivity
  have non:0<δ:=div_pos pos factor
  filter_upwards [menu i (late.trans lower) K upper Q anchor draw book limit diameter δ non] with per granted
  intro N top v money side P B modes x t widths cells sites grid divides digit place housed Z bounded head r d rp dr value
  let rows:=fun (d:ℕ)(s:Choices R k target.val)=>reading R κ pt N K i q d sites (t s) cells front grid digit place Z B (x s) target head s
  apply restore N per top (by omega) v money side P B x (fun _ d a=>rows d a true)
    (fun _ d a=>rows d a false) r d rp dr
  intro a
  have grantedB (J:Finset I)(o:J)(b:Fin (limit+1)):Paid (k:=k) R κ pt i K q per
      (fun j=>(B j).mode.val) front C diameter δ J o.val d b.val:=by
    rw [modes]
    exact granted J o ⟨d,by omega⟩ b
  have enough(J:Finset I):mass (fun j=>mass k ((B j).mode.val)) J+d ≤ limit:=by
    let names:=fun j=>(B j).mode.val
    change mass (fun j=>mass k (names j)) J+d≤limit
    rw [show names=words from modes]
    exact fits words J (dr.trans rp)
  have used:=WilsonOriginalCensusRosterFare.original R κ pt k N i K q per (fun j=>(B j).mode.val) front C
    diameter limit d δ non.le grantedB enough
    top (letter R target.val a) cells sites (t a) (widths a) grid divides digit place housed Z bounded B (x a) target head
  have exactRead : ‖rows d a true-rows d a false‖≤
      (∑s:Finset I,‖wages B (x a) target s‖)*(((limit:ℝ)+1)*δ):=used.2.1
  have refund:((limit:ℝ)+1)*δ=ε:=by dsimp [δ];field_simp
  rw [refund,mul_comm _ ε] at exactRead
  exact exactRead

end YM.Integration.WilsonIndependentCollarRestoredOrbit
end
