import YM.Integration.FVA1Physical.Sources.Round2.BasisWilson
import YM.Integration.FVA1Physical.Sources.Round2.PhysicalReadout

/-! A single finite-marker-table statement for the actual normalized C18
readout and the paper's independent coefficient vectors on the first block. -/

namespace YM.Integration.FVA1Physical.Round2

open Lattice RG YM.Wilson YM.Tree Marker Source Extra.Histories LocalLTE.Sail
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent Comparison.RG02
open FVA2.CityHistory YM.Integration.FVA1Physical.Wilson PertExtension.Series.Tested
open PhysicalNext.Repeat.Legato.Bandage.Harmonics
open scoped BigOperators

variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I] (B : Census I)

omit [DecidableEq I] in
/-- A unit basis source meets the amplitude part of the C18 admission test. -/
theorem basis_wants (A : StencilFamily G) {m n d K : ℕ} (a : I → FieldLabel A.family d)
    (o : ∀ j, I → Site (A.family.side j n)) (hreg : ∀ j, A.ref (a j).1.val ≤ m)
    (hload : Fintype.card I ≤ K) (hsite : ∀ j, o (m+1) j = (A.family.path.levels.clock.op m n).ratio.embed (o m j)) :
    (basisBatch A a (m+1) n o).Wants m A.ref K := by
  refine ⟨hreg,hload,?_,?_⟩
  · intro k j hki hk
    have : m = k := by omega
    subst k
    exact hsite j
  · intro j
    exact (Extra.Histories.Size.size_axis ((Labels.frames G).level (a j).1.val) (a j).2).le

/-- Componentwise agreement of the entire independently predicted Wilson
polynomial, with one estimate for every test chosen on the complete census. -/
theorem tested_basis_wilson_uniform (A : StencilFamily G) (L : Bulk.Chain A.family.path)
    (m d : ℕ) (q : ℝ) (hq : 0 < q) (r : ℕ) :
    ∃ δ C, 0 < δ ∧ 0 ≤ C ∧ ∀ (a : I → FieldLabel A.family d) (n : ℕ)
        (o : ∀ j, I → Site (A.family.side j n)),
      let S := A.family.path.levels.clock.op m n
      ∀ (F : Forest S.ratio) (t : S.Choices) (u : Pins G (A.family.side m n)),
        Bid.Larger (G := G) S → (∀ j, ‖u j‖ ≤ q) →
        let g := Pert.Asymptotics.regulatorRun A.family (m+1) n (m+1)
        g ≤ δ →
        let x := axesP G (A.family.side m n) u
        let Y := basisBatch A a (m+1) n o
        let V := placeLabels a (o (m+1))
        let D := MSMatch.SourceTop.datum B m n V F t x
        let Z : Poly B := fun s => basisFactor A a n o B (m:=m) s • peval (fun k => D.ordinaryCoefficient L r k s) r g
        let U := Integral.sample g x
        let exact := ((((A.family.path.rep (m+1) n m).eval U : ℂ)⁻¹) • gust A.family.path (m+1) n (m+1) (Y.raw B) m (Nat.le_succ m) U)
        Poly.price (fun _=>1) (exact-Z) ≤ C * g ^ (r+1) ∧
          ∀ w : B.Mode → ℂ, (∀ s, ‖w s‖ ≤ 1) → ‖modeTest w (exact-Z)‖ ≤ C * g ^ (r+1) := by
  obtain ⟨δ,C,hδ,hC,he⟩ := basis_moment_wilson_uniform A B L m d q hq r
  let count := (Fintype.card B.Mode : ℝ)
  refine ⟨δ,count*C,hδ,mul_nonneg (Nat.cast_nonneg _) hC,?_⟩
  intro a n o S F t u had hu g hδg x Y V D Z U exact
  have hm : exact = momentTable B Y m (Nat.le_succ m) U := physical_moment_table A.makes.wilson B Y m (Nat.le_succ m) U
  have h : Poly.price (fun _=>1) (exact-Z) ≤ (count*C)*g^(r+1) := by
    rw [hm]
    simp only [Poly.price,Poly.toll,Finset.prod_const_one,one_mul,Extra.Trajectories.part_sub]
    apply (Finset.sum_le_sum (fun s _ => he a s n o F t u had hu hδg)).trans
    simp [count, g, mul_assoc]
  exact ⟨h, fun w hw => (norm_modeTest_le_price w _ hw).trans h⟩

end YM.Integration.FVA1Physical.Round2
