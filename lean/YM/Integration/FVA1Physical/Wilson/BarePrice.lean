import YM.Integration.FVA1Physical.Wilson.MarkedBareMatch
import YM.Integration.RunFormalChain

/-! Uniform quantitative comparison directly against the independent
normalized Wilson coefficients on the bare tier. Physical stencil types are
chosen before the period; every insertion site may subsequently vary. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open YM.Lattice YM.RG YM.Wilson YM.Tree YM.Precision YM.Marker
open YM.Comparison.RG02 YM.FVA2.CityHistory YM.FormalOPE.RG10.InversionTop
open YM.RGComparison.Core16 YM.RGComparison.Core16.Spool
open YM.RGComparison.Core16.Parcel YM.RGComparison.Core16.Parcel.Oven
open YM.PertExtension.Series YM.PertExtension.Series.Tested
open scoped Classical BigOperators

variable {G : Gauge} {C : Family G} {ι : Type} {d m : ℕ}

/-- Put the same physical field types at arbitrary sites of a new torus. -/
def placeStencils {a b : Side} (U : ι → Stamp.Reservation C a d) (y : ι → Site b)
    (i : ι) : Stamp.Reservation C b d := ⟨(U i).height, (U i).admitted, (U i).leg, y i⟩

variable [Fintype ι] [DecidableEq ι] (R : Census ι)
    (U : ι → Stamp.Reservation C (C.side (m+1) 0) d)
    (hC : C.Makes) (hs : ∀ i, Bid.pop (C.localSection i))
variable {P : Oven (C.path.levels.clock.op m 0).patch} {X : P.Form G} (H : P.Offers X (C.path.levels.clock.op m 0).kernel)
    (Z : ChartRatio G) (hZ : LocalRatio Z) (r : ℕ)

private def WithinPrice (s : R.Mode) (δ A : ℝ) : Prop :=
  ∀ (L : Bulk.Chain C.path) (p : ℕ) (y : ι → Site (C.side (m+1) p))
    (F : Forest (C.path.levels.clock.op m p).ratio) (t : (C.path.levels.clock.op m p).Choices) (u : Pins G (C.side m p)),
    Bid.Larger (G := G) (C.path.levels.clock.op m p) → (∀ i, ‖u i‖ ≤ X.Q) → ∀ g, 0 < g → g ≤ δ →
    let x := axesP G (C.side m p) u
    let D := MSMatch.SourceTop.datum R m p (placeStencils U y) F t x
    ‖(MSMatch.SourceTop.torusVacuum (C := C) m p x g)⁻¹ •
        MSMatch.SourceTop.torusFull m p (placeStencils U y) x s.val g -
      peval (fun k => D.ordinaryCoefficient L r k s) r g‖ ≤ A * g ^ (r+1)

include hC hs H hZ in
private theorem mode_price (s : R.Mode) :
    ∃ δ A, 0 < δ ∧ 0 ≤ A ∧ WithinPrice (X := X) R U r s δ A := by
  let J := modeLamp R U hC hs s
  let B : Lumen.Stage := ⟨1, 0, le_rfl⟩
  obtain ⟨E, A, _, hA, hall⟩ := every J H B r hZ
  refine ⟨Forge.dollar E.L, A, Forge.dollar_pos _, hA, ?_⟩
  intro L p y F t u h hu g hg hδ
  let V := placeStencils U y
  let D := MSMatch.SourceTop.datum R m p V F t (axesP G _ u)
  let c := rank J (C.path.levels.clock.op m p) F X Z u (modeSite R V s)
  have q (k : ℕ) (hk : k ≤ r) : D.ordinaryCoefficient L r k s = c k :=
    normalized_coefficients R V hC hs u L F t s H h hu hZ hk
  have he : peval (fun k => D.ordinaryCoefficient L r k s) r g = peval c r g := by
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg (fun z : ℂ => g ^ k • z) (q k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  change ‖_ - peval (fun k => D.ordinaryCoefficient L r k s) r g‖ ≤ _
  rw [he, sourceRatio_eq_reads R V hC hs u s g]
  exact (hall (C.side m p) (C.side (m+1) p) (C.path.levels.clock.op m p).sizes h F u (modeSite R V s) hu).cost g hg hδ
    |>.trans_eq (mul_comm _ _)

include hC hs H hZ in
/-- One cutoff and constant for the complete finite marker census. They
precede the choice of periods, forests, tags, bounded coarse directions,
all insertion sites and the chain. The polynomial uses the normalized
`RG02.Bulk.Fk` coefficients of this very marked physical datum. -/
theorem normalized_uniform :
    ∃ δ A, 0 < δ ∧ 0 ≤ A ∧
      ∀ (s : R.Mode) (L : Bulk.Chain C.path) (p : ℕ)
        (y : ι → Site (C.side (m+1) p)) (F : Forest (C.path.levels.clock.op m p).ratio)
        (t : (C.path.levels.clock.op m p).Choices) (u : Pins G (C.side m p)),
        Bid.Larger (G := G) (C.path.levels.clock.op m p) → (∀ i, ‖u i‖ ≤ X.Q) → ∀ g, 0 < g → g ≤ δ →
        let x := axesP G (C.side m p) u
        let D := MSMatch.SourceTop.datum R m p (placeStencils U y) F t x
        ‖(MSMatch.SourceTop.torusVacuum (C := C) m p x g)⁻¹ •
            MSMatch.SourceTop.torusFull m p (placeStencils U y) x s.val g -
          peval (fun k => D.ordinaryCoefficient L r k s) r g‖ ≤ A * g ^ (r+1) := by
  classical
  letI : Nonempty R.Mode := ⟨R.quiet⟩
  choose δ A hδ hA hp using mode_price R U hC hs H Z hZ r
  let δ₀ := Finset.univ.inf' Finset.univ_nonempty δ
  refine ⟨δ₀, ∑ s, A s, (Finset.lt_inf'_iff _).2 (fun s _ => hδ s),
    Finset.sum_nonneg (fun s _ => hA s), ?_⟩
  intro s L p y F t u h hu g hg hsmall
  have q : δ₀ ≤ δ s := Finset.inf'_le _ (Finset.mem_univ s)
  exact (hp s L p y F t u h hu g hg (hsmall.trans q)).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ s))
      (pow_nonneg hg.le _))

/-- On the retained physical run the chart, stationary chain, field
calibration and analytic provider are all supplied. The direction bound
may be specified before either the period or the marker placement. -/
theorem run_uniform (A : PhysicalNext.Repeat.Legato.Run G)
    (V : ι → Stamp.Reservation A.family (A.family.side (m+1) 0) d)
    (q : ℝ) (hq : 0 < q) (r : ℕ) :
    ∃ δ B, 0 < δ ∧ 0 ≤ B ∧ ∀ (s : R.Mode) (p : ℕ)
      (y : ι → Site (A.family.side (m+1) p)),
      let S := A.family.path.levels.clock.op m p
      ∀ (F : Forest S.ratio) (t : S.Choices) (u : Pins G (A.family.side m p)),
        Bid.Larger (G := G) S → (∀ i, ‖u i‖ ≤ q) → ∀ g, 0 < g → g ≤ δ →
        let x := axesP G (A.family.side m p) u
        let D := MSMatch.SourceTop.datum R m p (placeStencils V y) F t x
        ‖(MSMatch.SourceTop.torusVacuum (C := A.family) m p x g)⁻¹ •
            MSMatch.SourceTop.torusFull m p (placeStencils V y) x s.val g -
          peval (fun k => D.ordinaryCoefficient (RunFormalChain.fromRun A) r k s) r g‖ ≤
            B * g ^ (r+1) := by
  let L := RunFormalChain.fromRun A
  obtain ⟨P⟩ := Oven.builtafter (A.family.path.levels.clock.op m 0).patch
  obtain ⟨X, hX, H⟩ := Oven.fund P (A.family.path.levels.blocks m 0).branches q hq
  obtain ⟨δ, B, hd, hB, h⟩ := normalized_uniform R V A.makes (fun i => Next.Foundations.valuation G i)
    H L.O L.receipt r
  refine ⟨δ, B, hd, hB, ?_⟩
  intro s p y S F t u hS hu
  exact h s L p y F t u hS (by simpa only [hX] using hu)

end YM.Integration.FVA1Physical.Wilson

