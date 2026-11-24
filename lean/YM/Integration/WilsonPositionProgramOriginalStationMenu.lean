import YM.Integration.WilsonPositionProgramMeteredPublicResponse
import YM.Integration.WilsonPositionProgramOriginalStationRadius
import Mathlib.Order.Filter.Curry

/-! Fixed physical position readings for a finite collection of graded fields.
Each true filed coordinate may depend on both physical regulators, and is used
unchanged in the finite and covered programs at every independent site. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramOriginalStationMenu
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Fountain
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Winding WilsonCoeffUV.Layout WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops WilsonPositionProgramThermometerCoordinates
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNominatedRoster (selected)
open WilsonPositionProgramNominatedWinding (unitFare)
open WilsonPositionProgramNominatedPublicScalar (finite)
open WilsonPositionProgramOriginalStationRadius (zoomFactor covers)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{e k u D:ℕ}
variable {I:Type} [Fintype I]


open WilsonPositionProgramNormalizedMaster (fee)
open WilsonPositionProgramNominatedMenuInvoice (issued)
variable {c:ℕ}
variable (arity:I→ℕ)(l d:(s:I)→Fin (arity s+1)→ℕ)(fit:∀s i,l s i<d s i)
local notation "Q" => fun s=>deck (G:=G) (l s) (d s) (fit s)

def difference (big:0<D)(φ:(s:I)→Wilt (Q s))(A:Group R.family c)
    (checked:A.station.checked f H A.horizon)(m N per n p k:ℕ)
    (source:(s:I)→ℕ→ℕ→Herit (Q s))(s:I)(t:ℕ)(i:Alma ((primes G).F 0)):ℝ:=
  let L:=R.family.path.levels
  let placed:=sceneGrow (covers R A checked) (φ s)
  let X:=source s N per
  finite R (l s) (d s) (fit s) m n p t D placed X i -
    PowerSeries.coeff t (lodgeIn L R.metals.O ((primes G).T 0) big placed
      (normalized L R.metals.O (Q s) X m) m m m k i)

theorem original (simple:G.Simple)(reading:RG05Preconstruction.ReadoutPurchase R.b)(paid:issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(cap:∀s,capP (Q s) ≤ k)
    (φ:(s:I)→Wilt (Q s))(apart:∀s i j,i≠j → Disjoint (tsupport (φ s i).ψ.val) (tsupport (φ s j).ψ.val)):
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1≤zz L m → ∀A:Group R.family c,A.station.k=m →
    ∀checked:A.station.checked f H A.horizon,∀(source:(s:I)→ℕ→ℕ→Herit (Q s))(money:(s:I)→Fin (arity s+1)→ℝ),
    (∀s N per,m<N → ∀i,fee (source s N per) e i ≤ money s i) → ∀ε:ℝ,0<ε →
    ∃K:ℕ,m≤K ∧ ∀ᶠ p:ℕ in atTop,∀(N per n:ℕ),m<N → K≤n →
      ∀s:I,∀t:Fin (e+1),∀i:Alma ((primes G).F 0),
        ‖difference R arity l d fit big φ A checked m N per n p k source s t i‖<ε:=by
  intro L
  choose Z B _ reprice using fun s:I=>WilsonPositionProgramOriginalStationRadius.original
    (c:=c) (f:=f) (H:=H) R simple (φ s) (apart s) 1
  have filed:=eventually_all.mpr (fun s:I=>WilsonPositionProgramMeteredPublicResponse.original
    R simple reading paid big rails (l s) (d s) (fit s) (cap s) zero_lt_one)
  filter_upwards [filed,eventually_all.mpr reprice] with m heard paidShape
  intro cash A date checked source money funded ε tol
  let ρ:=zoomFactor R A
  let ready:=covers R A checked
  let b(s:I):=max (Compar L.S (zz L) m m) (Z s*ρ)
  let fees(s:I)(i:Fin (arity s+1)):=ρ⁻¹^4*B s i
  let placed(s:I):=sceneGrow ready (φ s)
  have bought(s:I):Bough (Q s) (placed s) 1 (b s) (fees s) ∧
      ∀i j,i≠j → ClearDay (placed s i) (placed s j) (1*longLog L m+14):=
    (Classical.choose_spec (paidShape s A date checked)).2
  choose K _ all using fun s:I=>heard s cash (source s) (money s) (funded s) (b s) (fees s) ε tol
  let top:=max m (Finset.univ.sup K)
  refine ⟨top,le_max_left ..,?_⟩
  filter_upwards [eventually_all.mpr (fun s:I=>all s (placed s) (le_max_left ..) (bought s).1 (bought s).2)] with p landed
  intro N per n late mature s t i
  have floor:K s≤top:=(Finset.le_sup (f:=K) (mem_univ s)).trans (le_max_right ..)
  exact landed s N per n late (floor.trans mature) t i

theorem ordered (simple:G.Simple)(reading:RG05Preconstruction.ReadoutPurchase R.b)(paid:issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(cap:∀s,capP (Q s) ≤ k)
    (φ:(s:I)→Wilt (Q s))(apart:∀s i j,i≠j → Disjoint (tsupport (φ s i).ψ.val) (tsupport (φ s j).ψ.val)):
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1≤zz L m → ∀A:Group R.family c,A.station.k=m →
    ∀checked:A.station.checked f H A.horizon,∀(source:(s:I)→ℕ→ℕ→Herit (Q s))(money:(s:I)→Fin (arity s+1)→ℝ),
    (∀s N per,m<N → ∀i,fee (source s N per) e i ≤ money s i) →
    ∀(s:ℕ×ℕ→I)(t:ℕ×ℕ→Fin (e+1))(i:ℕ×ℕ→Alma ((primes G).F 0)),
      Tendsto (fun q:ℕ×ℕ=>difference R arity l d fit big φ A checked m q.2 q.1 q.2 q.1 k
        source (s q) (t q) (i q)) ((atTop:Filter ℕ).curry atTop) (𝓝 0):=by
  intro L
  filter_upwards [original (c:=c) (f:=f) (H:=H) R arity l d fit simple reading paid big rails cap φ apart] with m sale
  intro strip A date checked source money funded s t i
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  obtain ⟨K,floor,hear⟩:=sale strip A date checked source money funded ε pos
  apply eventually_curry_iff.mpr
  filter_upwards [hear] with p estimate
  filter_upwards [eventually_ge_atTop (K+1)] with N top
  rw [dist_zero_right]
  exact estimate N p N (by omega) (by omega) _ _ _

end YM.Integration.WilsonPositionProgramOriginalStationMenu
end
