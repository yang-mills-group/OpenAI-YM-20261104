import YM.Integration.WilsonPositionProgramUniformWindingTable
import YM.Integration.WilsonPositionProgramWindingSlotScale
import YM.Integration.WilsonPositionProgramNominatedReporter

/-! The numerical column can depend on both original regulators. The winding
test holds on each actual copy for all such columns and every internal cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramNominatedWinding
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Winding WilsonCoeffUV.Layout WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops WilsonPositionProgramThermometerCoordinates
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonPositionProgramNominatedRoster (selected selected_fee)
open WilsonMarkedIndependentMixedMomentTensor (Tensor)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{a e:ℕ}

def unitFare:Credit:=⟨0,2,by norm_num⟩

def physical (m q:ℕ):ℕ:=max (m+1) (Nat.unpair (q-m)).1
def period (m q:ℕ):ℕ:=(Nat.unpair (Nat.unpair (q-m)).2).1
def age (m q:ℕ):ℕ:=max m (Nat.unpair (Nat.unpair (q-m)).2).2
def address (m N p n:ℕ):ℕ:=m+Nat.pair N (Nat.pair p n)

theorem active (m N p n:ℕ)(h:m<N)(h':m≤n):
    physical m (address m N p n)=N ∧ period m (address m N p n)=p ∧ age m (address m N p n)=n:=by
  simp [physical,period,age,address,Nat.unpair_pair,max_eq_right h',h]

def output (R:Run G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)(m b n D:ℕ)
    (φ:Wilt (deck (G:=G) l d fit))(X:Herit (deck (G:=G) l d fit)):Era G (Vote D):=
  let L:=R.family.path.levels
  AutumnDay L R.metals.O φ (normalized L R.metals.O (deck (G:=G) l d fit) X m n) m b n D

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (child:Fin (a+1)→Fin 3)(d:Fin (a+1)→ℕ)(fit:∀i,levels (child i)<d i)
    (δ η:ℝ)(pos:0<η)
    (income:WilsonPositionProgramUniformWindingTable.Complete R (levels ∘ child) d fit e unitFare δ):
    let Q:=deck (G:=G) (levels ∘ child) d fit
    let L:=R.family.path.levels
    ∀ᶠ b:ℕ in atTop,∀m:ℕ, b ≤ m →
    ∃s:ℝ,0<s ∧ ∀A:Group R.family 6,A.station.k=m → A.station.checked f H A.horizon →
    ∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(φ:Wilt Q),(∀i j,i≠j → ClearDay (φ i) (φ j) (δ*longLog L m+14)) →
    ∀(D t r:ℕ),t≤e → ∀z:Fin r→YForest G,∃C:ℝ,0≤C ∧ ∀ᶠ p:ℕ in atTop,
    ∀N per n:ℕ,m<N → m≤n →
      let Y:=output R (levels ∘ child) d fit m b n D φ (selected R child d fit A m N per phase)
      ‖Y.1 (R.family.side b p) t r (slideC (R.family.side b p) z)-Y.2 t r z‖≤C*catchW s (R.family.side b p):=by
  intro Q L
  obtain ⟨c,charge⟩:=eventually_atTop.mp (WilsonPositionProgramThermometerCoordinates.original (f:=f) (H:=H) R simple η pos e
      (fun j=>levels j+1) (fun _=>Nat.lt_succ_self _))
  obtain ⟨c',scale⟩:=eventually_atTop.mp (WilsonPositionProgramWindingSlotScale.original R simple v paid (levels ∘ child) d fit e)
  filter_upwards [income,eventually_ge_atTop c,eventually_ge_atTop c'] with b issued cb cb'
  intro m bm
  have charged:=charge m (cb.trans bm)
  have scales:=scale m (cb'.trans bm)
  obtain ⟨s,hs,hear⟩:=issued m bm
  refine ⟨s,hs,?_⟩
  intro A date checked phase φ clear D t r ht z
  let w(i:Fin (a+1)):ℝ:=max 1 (price R e (child i)*‖phase (child i)‖*((L.clock.hatBeta m)^η*salary R A))
  have wp(i):0<w i:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  let X(q:ℕ):Herit Q:=selected R child d fit A m (physical m q) (period m q) phase
  let Y(q:ℕ):Herit Q:=onSlots Q (X q) (fun i=>(w i)⁻¹)
  have bound(q i):fee (X q) e i ≤ w i:=by
    rw [show fee (X q) e i=_ from selected_fee R child d fit A m (physical m q) (period m q) e phase i]
    exact (charged A date checked _ _ ((Nat.lt_succ_self m).trans_le (le_max_left ..)) phase (child i)).trans (le_max_right ..)
  have bill(q i):WilsonConditionalTaylorSeparatedPurchase.fee (Q i) (Y q i) e ≤ unitFare.buy (zz L m):=by
    simpa only [unitFare,Credit.buy,pow_zero,mul_one] using WilsonPositionProgramWindingSlotScale.residual Q (X q) w wp (bound q) i
  have low(q):m≤age m q:=le_max_left ..
  have funds:Tensor G (Vote D) m e (R.family.side b) (fun p=>catchW s (R.family.side b p))
      (fun q=>output R (levels ∘ child) d fit m b (age m q) D φ (Y q)):=
    (hear Y (age m) (fun q _=>low q) (fun q _=>bill q) φ clear).2 D
  let total:=∏i,w i
  obtain ⟨C,hC,priced⟩:=WilsonMarkedIndependentMixedMomentTensor.smul total funds t ht r z
  refine ⟨C,hC,?_⟩
  filter_upwards [priced] with p allq
  intro N per n mN mn bank
  let q:=address m N per n
  obtain ⟨top,rep,atn⟩:=active m N per n mN mn
  have valid:m≤q:=Nat.le_add_right ..
  have held:= (allq q valid).2.2
  let small:=output R (levels ∘ child) d fit m b (age m q) D φ (Y q)
  have same:bank=total • small:=by
    change output R (levels ∘ child) d fit m b n D φ _=_
    have auth:=scales b (age m q) D bm (low q) (X q) w φ wp
    change output R (levels ∘ child) d fit m b (age m q) D φ (X q)=total • small at auth
    rw [←auth]
    simp only [X,q,top,rep,atn]
  rw [same]
  exact held

end YM.Integration.WilsonPositionProgramNominatedWinding
end
