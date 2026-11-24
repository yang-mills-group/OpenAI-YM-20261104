import YM.Integration.FVA1Physical.Wilson.BarePrice

/-! Uniformity in all basis-field choices through a fixed finite field
horizon, with source positions free to vary on each period torus. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open YM.Lattice YM.Tree YM.Marker YM.FVA2.CityHistory
open YM.FormalOPE.RG10.InversionTop YM.PertExtension.Series.Tested
open scoped Classical BigOperators

variable {G : Gauge} {ι : Type} {d m : ℕ}

/-- A choice of a physical field through the specified horizon, without
committing to a period or a position. -/
abbrev FieldLabel (C : Family G) (d : ℕ) := Σ h : Fin (d+1), (C.labels.level h.val).Index

def placeLabels {C : Family G} {n : Side} (a : ι → FieldLabel C d) (y : ι → Site n)
    (i : ι) : Stamp.Reservation C n d :=
  ⟨(a i).1.val, Nat.le_of_lt_succ (a i).1.isLt, (a i).2, y i⟩

variable [Fintype ι] [DecidableEq ι] (R : Census ι) (A : PhysicalNext.Repeat.Legato.Run G)

/-- Every order and cap on the external coarse field give one error bound
for every basis-field assignment through the finite horizon, every mixed
mode, period, forest, tag, and set of sites on the same retained run. -/
theorem horizon_uniform (m d : ℕ) (q : ℝ) (hq : 0 < q) (r : ℕ) :
    ∃ δ B, 0 < δ ∧ 0 ≤ B ∧ ∀ (a : ι → FieldLabel A.family d) (s : R.Mode) (p : ℕ)
      (y : ι → Site (A.family.side (m+1) p)),
      let S := A.family.path.levels.clock.op m p
      ∀ (F : Forest S.ratio) (t : S.Choices) (u : Pins G (A.family.side m p)),
        Bid.Larger (G := G) S → (∀ i, ‖u i‖ ≤ q) → ∀ g, 0 < g → g ≤ δ →
        let x := axesP G (A.family.side m p) u
        let V := placeLabels a y
        let D := MSMatch.SourceTop.datum R m p V F t x
        ‖(MSMatch.SourceTop.torusVacuum (C := A.family) m p x g)⁻¹ •
            MSMatch.SourceTop.torusFull m p V x s.val g -
          peval (fun k => D.ordinaryCoefficient (RunFormalChain.fromRun A) r k s) r g‖ ≤
            B * g ^ (r+1) := by
  classical
  letI : Nonempty (FieldLabel A.family d) := ⟨⟨0, 0⟩⟩
  let anchor := fun _ : ι => (0 : Site (A.family.side (m+1) 0))
  choose δ cap hδ hcap hp using fun a : ι → FieldLabel A.family d =>
    run_uniform (m := m) R A (placeLabels a anchor) q hq r
  let δ₀ := Finset.univ.inf' Finset.univ_nonempty δ
  refine ⟨δ₀, ∑ a, cap a, (Finset.lt_inf'_iff _).2 (fun a _ => hδ a),
    Finset.sum_nonneg (fun a _ => hcap a), ?_⟩
  intro a s p y S F t u hS hu g hg hsmall
  have hle : δ₀ ≤ δ a := Finset.inf'_le _ (Finset.mem_univ a)
  exact (hp a s p y F t u hS hu g hg (hsmall.trans hle)).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun z _ => hcap z) (Finset.mem_univ a))
      (pow_nonneg hg.le _))

end YM.Integration.FVA1Physical.Wilson

