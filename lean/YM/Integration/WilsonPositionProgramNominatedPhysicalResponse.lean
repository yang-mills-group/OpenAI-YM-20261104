import YM.Integration.WilsonPositionProgramNominatedPhysicalProfile

/-! A finite menu of physical proper and full faces uses identical incoming
coordinates, one internal cutoff and the actual original period and UV order. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramNominatedPhysicalResponse
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
open WilsonPositionProgramNominatedPhysicalProfile (zoomFactor covers)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{e k u D:ℕ}
variable {I:Type} [Fintype I]

section
variable (arity:I→ℕ)(child:(s:I)→Fin (arity s+1)→Fin 3)(d:(s:I)→Fin (arity s+1)→ℕ)
    (fit:∀s i,levels (child s i)<d s i)
local notation "Q" => fun s=>deck (G:=G) (levels ∘ child s) (d s) (fit s)

def difference (big:0<D)(φ:(s:I)→Wilt (Q s))(A:Group R.family 6)
    (checked:A.station.checked f H A.horizon)(m N per n p k:ℕ)
    (phase:Fin 3→ℂ →L[ℝ] ℝ)(s:I)(t:ℕ)(i:Alma ((primes G).F 0)):ℝ:=
  let L:=R.family.path.levels
  let placed:=sceneGrow (covers R A checked) (φ s)
  let X:=selected R (child s) (d s) (fit s) A m N per phase
  finite R (levels ∘ child s) (d s) (fit s) m n p t D placed X i -
    PowerSeries.coeff t (lodgeIn L R.metals.O ((primes G).T 0) big placed
      (normalized L R.metals.O (Q s) X m) m m m k i)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(cap:∀s,capP (Q s) ≤ k)(δ η:ℝ)(pos:0<η)
    (income:∀s,WilsonPositionProgramUniformWindingTable.Complete R (levels ∘ child s) (d s) (fit s) e unitFare δ)
    (φ:(s:I)→Wilt (Q s))(apart:∀s i j,i≠j → Disjoint (tsupport (φ s i).ψ.val) (tsupport (φ s j).ψ.val)):
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1 ≤ zz L m →
    ∀A:Group R.family 6,A.station.k=m → ∀checked:A.station.checked f H A.horizon,
    ∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(ε:ℝ),0<ε →
    ∃K:ℕ,m≤K ∧ ∀ᶠ p:ℕ in atTop,∀(N per n:ℕ),m < N → K ≤ n →
      ∀s:I,∀t:Fin (e+1),∀i:Alma ((primes G).F 0),
        ‖difference R arity child d fit big φ A checked m N per n p k phase s t i‖<ε:=by
  intro L
  choose Z B _ reprice using fun s:I=>WilsonPositionProgramNominatedPhysicalProfile.original
    (f:=f) (H:=H) R simple (φ s) (apart s) δ
  have filed:=eventually_all.mpr (fun s:I=>WilsonPositionProgramNominatedPublicScalar.original
    (f:=f) (H:=H) R simple v paid big rails (child s) (d s) (fit s) (cap s) δ η pos (income s))
  filter_upwards [filed,eventually_all.mpr reprice] with m heard paidShape
  intro cash A date checked phase ε tol
  let ρ:=zoomFactor R A
  let ready:=covers R A checked
  let b(s:I):=max (Compar L.S (zz L) m m) (Z s*ρ)
  let fees(s:I)(i:Fin (arity s+1)):=ρ⁻¹^4*B s i
  let placed(s:I):=sceneGrow ready (φ s)
  have bought(s:I):Bough (Q s) (placed s) 1 (b s) (fees s) ∧
      ∀i j,i≠j → ClearDay (placed s i) (placed s j) (δ*longLog L m+14):=
    (Classical.choose_spec (paidShape s A date checked)).2
  choose K low all using fun s:I=>heard s cash A date checked phase (b s) (fees s) ε tol
  let top:=max m (Finset.univ.sup K)
  refine ⟨top,le_max_left ..,?_⟩
  filter_upwards [eventually_all.mpr (fun s:I=>all s (placed s) (le_max_left ..) (bought s).1 (bought s).2)] with p landed
  intro N per n high mature s t i
  have floor:K s≤top:=(Finset.le_sup (f:=K) (mem_univ s)).trans (le_max_right ..)
  exact landed s N per n high (floor.trans mature) t i

end
end YM.Integration.WilsonPositionProgramNominatedPhysicalResponse
end
