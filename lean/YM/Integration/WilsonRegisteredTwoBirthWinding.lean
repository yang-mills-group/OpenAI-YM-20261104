import YM.Integration.WilsonTwoBirthWindingHearing
import YM.Integration.WilsonLimitConstruction.FundedInheritedWinding
import YM.Integration.WilsonLimitConstruction.FundedPointSourceClock

/-! Winding of the registered Wilson curvature pair with different birth dates,
on the original measured realm issuing the marked and adjacent packet budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRegisteredTwoBirthWinding
open Function Filter Finset Set Lattice RG RG.Supply Wilson Source Labels Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Blue FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction
open FundedNeutralCostRun IndependentSourcePathFamily
open scoped Topology BigOperators Classical

variable {G : Gauge} {v : ℕ} {R : Run G}
variable {deck : MS.Local.Physical.Deck G}

abbrev orbits (R : Run G) (grades weights : Fin v → ℕ) :=
  ActualRunQlocalNativeTuple.orbit (FundedPointMarkedSeed.reference R grades weights)

def traces {D k : Fin v → ℕ} {e m : ℕ} {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m}
    {A : ℝ} (T : Input Q hm univ k D A) (R : Run G) (J : Finset (Fin v)) (o : Fin v)
    (i r per : ℕ) (σ B : ℝ) : Prop :=
  let n := R.family.side m per
  let row := WilsonFiniteIncomingWindingCurrent.row Q.draws Q.paid m (m+2) n
    (fun z => T.familyAt (PeriodicMarkedWinding.roots n z o)) k J o i r
  ∀ (a : ℕ) (W : Credit) (u : ℝ), (σ/32/2/2)⁻¹ ≤ W.buy u → 1 ≤ u →
    let fee := WilsonFiniteIncomingWindingCurrent.price G r a J o n σ B W u
    PostMark J o r row (σ/256) fee a ∧
    ∀ (x : Cover) (v : Fence (Hooks G) J o r → SignedRootedWindingReadout.Tests D)
      (V : ℝ), 0 ≤ V → (∀ b, SignedRootedWindingReadout.amplitude J (v b) ≤ V) →
      ∀ ξ : Fence (Hooks G) J o r → ℂ, (∀ b, ‖ξ b‖ ≤ 1) →
      let f := fun b => ξ b * SignedRootedWindingReadout.read J (v b) (towerV J o r row x b)
      Summable f ∧ ‖∑' b, f b‖ ≤ V*fee

variable {I : Inventory G} {D : FundedPacketWidthPrices.Diagrams G}
    {prior : FundedPacketWidthPrices.Ceilings G} {E K S : ℕ → ℕ}
    (p : Purchase (FundedPacketWidthPrices.augment I D (FundedRunPacketWidths.ceilings prior E K S)) R)
    (j : ℕ) (Γ : Census (Fin v)) (k : Fin v → ℕ) (req : Request (Fin v))
    (scale : Block Γ k (E j) → Gear G → ℝ) (degree derivative : Block Γ k (E j) → ℕ)
    (c q : ℕ) (P : MS.Land.Prescription deck)
    (grades weights : Fin v → ℕ) (labs : Fin v → MS.Rake.Label deck) (μ : ℝ)
    (normal : Fin v → ℂ) (quad : Fin v → Bool)

/-- Both curvature source lists are the measured Wilson point data. The same table and
signed budget apply before every actual period and both independently chosen site lists. -/
theorem original (H : Credit) (menu : Gear G → ℝ) (hmenu : ∀ L, 0 < menu L)
    (J : Finset (Fin v)) (o : Fin v) (ho : o ∈ J) (i r : ℕ) (hi : i ≤ E j) :
    ∃ (cap : Gear G → ℝ) (quiet : Credit), (∀ L, 0 < cap L) ∧ ∀ m,
      FundedInheritedWinding.Stage p j Γ k (orbits R grades weights) req
        scale degree derivative c q m →
      ∃ (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
        (cap (Q.mint (m+1) (hm.trans (Nat.le_succ m))).gear ≤ Q.cash H (m+1) →
        ∀ (transport oldOrders freshOrders : Fin v → ℕ) (old : Finset (Fin v))
          (cells : (Fin v → Cover) → Fin v → Site (loose Q.draws m).L),
        ∃ (A : ℝ) (T : Input Q hm univ k (NativeMarkedAddressTokens.axes (orbits R grades weights)) A)
          (d : ℕ) (C B σ : ℝ), 0 ≤ A ∧ T.offsets = cells ∧ 0 ≤ C ∧ 1 ≤ B ∧ 0 < σ ∧
          ∀ per, FundedInheritedWinding.Invoice p j Γ k (orbits R grades weights) req
            scale degree derivative c q Q hm (m+2) per (by omega) A T ∧
          traces T R J o i r per σ (C * (max 1 (Q.cash quiet (m+1)))^d * B^J.card *
            rimJ (ratioHigh Q.draws Q.paid (m+2) m) i r) ∧
          ∀ (oldSites : Fin v → Site (R.family.side (m+2) per))
            (freshSites : Fin v → Site (R.family.side (m+1) per)),
          let X := FundedOriginalMarkedInput.chosen P
            (FundedPointMarkedSeed.datum R grades weights per (m+2) oldSites) labs
            (μ - R.family.S.scale (m+2)) oldOrders normal quad
          let Y := FundedOriginalMarkedInput.chosen P
            (FundedPointMarkedSeed.datum R grades weights per (m+1) freshSites) labs
            (μ - R.family.S.scale (m+1)) freshOrders normal quad
          (∀ y S, S ⊆ old → T.familyAt y S =
            Gears Q.draws Q.paid transport k (m+2) (m+2) (m+1) (independent X)
              (chartIn (loose Q.draws m) y (cells y)) S) ∧
          (∀ y z, z ∉ old → T.familyAt y {z} = single Y z
            (chartIn (loose Q.draws m) y (cells y) z))) := by
  classical
  let seed := FundedPointMarkedSeed.reference R grades weights
  have theorem' := WilsonTwoBirthWindingHearing.original
    (D:=NativeMarkedAddressTokens.axes (orbits R grades weights)) (k:=k) (e:=E j)
    (I:=fun z => FundedOriginalMarkedInput.Count seed labs z)
    (U:=fun z => FundedOriginalMarkedInput.Count seed labs z) (J:=J) (o:=o) (i:=i) (r:=r)
    H menu hmenu
  obtain ⟨cap, quiet, hcap, hearing⟩ := theorem'
  refine ⟨cap, quiet, hcap, ?_⟩
  intro m stage
  obtain ⟨Q,hm,levels,ratio,_,_,cloze,_,_,_,_,issue⟩ := stage
  refine ⟨Q, hm, levels, ratio, ?_⟩
  intro paid transport oldOrders freshOrders old cells
  let X := FundedPointMarkedSeed.source R P grades weights labs
    (μ - R.family.S.scale (m+2)) oldOrders normal quad
  let Y := FundedPointMarkedSeed.source R P grades weights labs
    (μ - R.family.S.scale (m+1)) freshOrders normal quad
  obtain ⟨A,T,hA,offsets,previous,fresh,d,C,B,σ,hC,hB,hσ,heard⟩ :=
    hearing Q m hm paid cloze transport X Y (fun z _ => Nat.le_add_left _ (k z))
      (fun z _ => Nat.le_add_left _ (k z)) (fun _ => 1) (fun _ => zero_lt_one) old cells ho hi
  refine ⟨A,T,d,C,B,σ,hA,offsets,hC,hB,hσ,?_⟩
  intro per
  refine ⟨issue (m+2) per (by omega) A T hA, heard (R.family.side m per), ?_⟩
  intro oldSites freshSites
  dsimp only
  rw [FundedPointMarkedSeed.same, FundedPointMarkedSeed.same]
  exact ⟨previous, fresh⟩

end YM.Integration.WilsonRegisteredTwoBirthWinding
end

