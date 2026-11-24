import YM.Integration.FVA1Physical.Sources.Round2.BasisFields
import YM.Integration.FVA1Physical.Sources.Round2.StencilOrder

/-! Uniform error of actual one-block C18 posterior basis moments against
independently prescribed Wilson coefficients, at the physical bare coupling. -/

namespace YM.Integration.FVA1Physical.Round2

open Lattice RG YM.Wilson YM.Tree Marker Source Extra.Histories LocalLTE.Sail
open FVA2.CityHistory Comparison.RG02 PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open YM.Integration.FVA1Physical.Wilson PertExtension.Series.Tested
open PhysicalNext.Repeat.Legato.Bandage.Harmonics
open scoped BigOperators

variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I] (A : StencilFamily G) (B : Census I)

private theorem measured_scale (N n : ℕ) :
    let g := Pert.Asymptotics.regulatorRun A.family N n N
    let θ := A.family.path.levels.clock.threshold N
    0 ≤ g / θ ∧ g / θ ≤ 2 := by
  let H := A.family.path
  let b := H.β N n N
  let x := H.levels.clock.hatBeta N
  have hb := Local.RealStep.actual_positive A.family N n N A.makes le_rfl
  have hx : 0 < x := zero_lt_one.trans_le (H.levels.fits.delayed N).le
  have hband : x / 2 ≤ b := (A.makes.wilson.represents N n N le_rfl).band.1
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hroot : Real.sqrt x ≤ 2 * Real.sqrt b := by
    nlinarith [Real.sq_sqrt hx.le,Real.sq_sqrt (show 0 ≤ b from hb.le),sq_nonneg (Real.sqrt x - 2*Real.sqrt b)]
  have hθ : H.levels.clock.hatCoupling N ≤ H.levels.clock.threshold N :=
    le_mul_of_one_le_right (inv_nonneg.mpr hsx.le) (Real.one_le_exp (sq_nonneg _))
  have ht := (H.levels.budget N).threshold_pos
  refine ⟨div_nonneg (inv_nonneg.mpr hsb.le) ht.le, (div_le_iff₀ ht).2 ?_⟩
  have hr : 1 / Real.sqrt b ≤ 2 / Real.sqrt x := (div_le_div_iff₀ hsb hsx).mpr (by linarith only [hroot])
  change (Real.sqrt b)⁻¹ ≤ 2*H.levels.clock.threshold N
  apply le_trans _ (mul_le_mul_of_nonneg_left hθ zero_le_two)
  simpa [Calendar.hatCoupling, x, div_eq_mul_inv] using hr

private theorem basisFactor_bound {m d n : ℕ} (a : I → FieldLabel A.family d)
    (o : ∀ j, I → Site (A.family.side j n)) (s : B.Mode) :
    0 ≤ basisFactor A a n o B (m:=m) s ∧ basisFactor A a n o B (m:=m) s ≤
       (2:ℝ) ^ (Fintype.card I * horizonDegree G d) := by
  have hp := measured_scale A (m+1) n
  let z := Pert.Asymptotics.regulatorRun A.family (m+1) n (m+1) / A.family.path.levels.clock.threshold (m+1)
  let N := horizonDegree G d
  have hs (i : I) : MSMatch.SourceTop.grade (placeLabels a (o (m+1))) i ≤ N := by
    let f := (Labels.frames G).level (a i).1.val
    have h := Finset.le_sup (f:=fun j : f.Index => (f.grades j).2) (Finset.mem_univ (a i).2)
    exact h.trans (Finset.single_le_sum (fun k _ => Nat.zero_le (Extra.Multi.BasisCost.slots ((Labels.frames G).level k)))
      (Finset.mem_range.mpr (a i).1.isLt))
  change 0 ≤ ∏ i ∈ s.val, z ^ _ ∧ ∏ i ∈ s.val, z ^ _ ≤ _
  refine ⟨Finset.prod_nonneg (fun i _ => pow_nonneg hp.1 _), ?_⟩
  calc
    _ ≤ ∏ _i ∈ s.val, (2:ℝ)^N := Finset.prod_le_prod (fun i hi => pow_nonneg hp.1 _)
      (fun i hi => (pow_le_pow_left₀ hp.1 hp.2 _).trans (pow_le_pow_right₀ one_le_two (hs i)))
    _ = (2:ℝ)^(s.val.card * N) := by rw [Finset.prod_const,← pow_mul, Nat.mul_comm]
    _ ≤ _ := pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_right _ (Finset.card_le_univ s.val))

private theorem stencil_uniform (L : Bulk.Chain A.family.path) (m d : ℕ) (q : ℝ) (hq : 0 < q) (r : ℕ) :
    ∃ δ C, 0 < δ ∧ 0 ≤ C ∧ ∀ (a : I → FieldLabel A.family d) (s : B.Mode) (n : ℕ)
        (y : I → Site (A.family.side (m+1) n)),
      let S := A.family.path.levels.clock.op m n
      ∀ (F : Forest S.ratio) (t : S.Choices) (u : Pins G (A.family.side m n)),
        Bid.Larger (G := G) S → (∀ j, ‖u j‖ ≤ q) → ∀ g, 0 < g → g ≤ δ →
        let x := axesP G (A.family.side m n) u
        let V := placeLabels a y
        let D := MSMatch.SourceTop.datum B m n V F t x
        ‖(MSMatch.SourceTop.torusVacuum (C := A.family) m n x g)⁻¹ • MSMatch.SourceTop.torusFull m n V x s.val g -
          peval (fun k => D.ordinaryCoefficient L r k s) r g‖ ≤ C * g ^ (r+1) := by
  classical
  obtain ⟨P⟩ := Oven.builtafter (A.family.path.levels.clock.op m 0).patch
  obtain ⟨X,hX,H⟩ := Oven.fund P (A.family.path.levels.blocks m 0).branches q hq
  letI : Nonempty (FieldLabel A.family d) := ⟨⟨0,0⟩⟩
  let zeroSite := fun _ : I => (0 : Site (A.family.side (m+1) 0))
  choose δ C hd hC h using fun a : I → FieldLabel A.family d => normalized_uniform B
    (placeLabels a zeroSite) A.makes (fun i => Next.Foundations.valuation G i) H L.O L.receipt r
  let η := Finset.univ.inf' Finset.univ_nonempty δ
  refine ⟨η, ∑ a, C a, (Finset.lt_inf'_iff _).2 (fun a _ => hd a), Finset.sum_nonneg (fun a _ => hC a), ?_⟩
  intro a s n y S F t u hS hu g hg hη
  have hδ : η ≤ δ a := Finset.inf'_le _ (Finset.mem_univ a)
  exact (h a s L n y F t u hS (by simpa only [hX] using hu) g hg (hη.trans hδ)).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ a)) (pow_nonneg hg.le _))

/-- Each incoming measured coupling within the fixed local interval yields a
price with the same constant for every period, basis choice, origin and mode.
The polynomial uses the independently normalized Wilson datum of this run. -/
theorem basis_moment_wilson_uniform (L : Bulk.Chain A.family.path) (m d : ℕ) (q : ℝ) (hq : 0 < q) (r : ℕ) :
    ∃ δ C, 0 < δ ∧ 0 ≤ C ∧ ∀ (a : I → FieldLabel A.family d) (s : B.Mode)
        (n : ℕ) (o : ∀ j, I → Site (A.family.side j n)),
      let S := A.family.path.levels.clock.op m n
      ∀ (F : Forest S.ratio) (t : S.Choices) (u : Pins G (A.family.side m n)),
        Bid.Larger (G := G) S → (∀ j, ‖u j‖ ≤ q) →
        let g := Pert.Asymptotics.regulatorRun A.family (m+1) n (m+1)
        g ≤ δ →
        let x := axesP G (A.family.side m n) u
        let Y := basisBatch A a (m+1) n o
        let V := placeLabels a (o (m+1))
        let D := MSMatch.SourceTop.datum B m n V F t x
        ‖(momentTable B Y m (Nat.le_succ m) (Integral.sample g x)).part s -
          basisFactor A a n o B (m:=m) s • peval (fun k => D.ordinaryCoefficient L r k s) r g‖ ≤
          C * g ^ (r+1) := by
  obtain ⟨δ,C,hδ,hC,he⟩ := stencil_uniform A B L m d q hq r
  let b := (2:ℝ) ^ (Fintype.card I * horizonDegree G d)
  have hb : 0 ≤ b := pow_nonneg zero_le_two _
  refine ⟨δ,b*C,hδ,mul_nonneg hb hC,?_⟩
  intro a s n o S F t u had hu g hg x Y V D
  rw [basis_moment_eq_torus A a n o B, ← smul_sub, norm_smul]
  have h := basisFactor_bound A B a o (m := m) s
  rw [Real.norm_of_nonneg h.1]
  have hp := Local.RealStep.coupling_pos A.family (m+1) n (m+1) A.makes le_rfl
  exact (mul_le_mul h.2 (he a s n (o (m+1)) F t u had hu g hp hg) (norm_nonneg _) hb).trans_eq (mul_assoc ..).symm

end YM.Integration.FVA1Physical.Round2
