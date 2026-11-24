import YM.Integration.WilsonFiniteCommonKineticReset

/-! At the first genuinely inherited date, the previous independently computed
quiet action is paired with its covered action. The width and the input of the
numerical invoice are fixed before the period is admitted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstInheritedVacuum
open Function Filter Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Winding
open scoped Classical BigOperators

variable {G : Gauge} {i r e : ℕ} {E : Credit}

def rent (Q : Realm G (e+1) E) (m : ℕ) (U : Fin (i+1) → Credit) (a : ℕ) : ℝ :=
  if h : a ≤ i then Q.cash (U ⟨a,Nat.lt_succ_of_le h⟩) m else 0

theorem original (hi : i ≤ e) (H E : Credit) (u : Gear G → ℝ) (hu : ∀ I, 0 < u I) :
    ∃ (c : Gear G → ℝ) (U : Fin (i+1) → Credit), (∀ I, 0 < c I) ∧
      ∀ (Q : Realm G (e+1) E) (m : ℕ) (hm : Q.anchor ≤ m),
        let I := (Q.mint m hm).gear
        c I ≤ Q.cash H m → ∀ n : Side,
          Sight ((story Q.draws Q.paid (m+1) m).1 n i (r+1))
            (actionW Q.draws Q.paid (m+1) m i (r+1)) (c I)⁻¹
            (WilsonFiniteCommonKineticReset.fee (back (Kstar (freshet Q.draws Q.paid (m+1) m)))
              i (r+1) (rent Q m U)) := by
  classical
  choose s bound U tariff step using fun a : Fin (i+1) =>
    WilsonFiniteBareHistory.first (G:=G) (i:=a.val) (r:=r+1)
      ((Nat.lt_succ_iff.mp a.isLt).trans hi) H E u hu
  let total (I : Gear G) := 1 + ∑ a, |bound a I|
  have enough (I : Gear G) (a : Fin (i+1)) : bound a I ≤ total I := by
    calc
      bound a I ≤ |bound a I| := le_abs_self _
      _ ≤ ∑ b, |bound b I| := Finset.single_le_sum (fun b _ => abs_nonneg (bound b I)) (Finset.mem_univ a)
      _ ≤ total I := le_add_of_nonneg_left zero_le_one
  refine ⟨total,U,(fun I => by dsimp [total]; positivity),?_⟩
  intro Q m hm I paid n
  apply WilsonFiniteCommonKineticReset.retained Q.draws Q.paid (Nat.lt_succ_self m) n i r
  intro a ha
  let k : Fin (i+1) := ⟨a,Nat.lt_succ_of_le ha⟩
  have area := step k Q m n hm ((enough I k).trans paid)
  have narrow : (total I)⁻¹ ≤ s k I := by
    have := inv_anti₀ (inv_pos.mpr (tariff k I).1) ((tariff k I).2.trans (enough I k))
    simpa only [inv_inv] using this
  simpa only [rent,dif_pos ha,k] using area.mono narrow

end YM.Integration.WilsonFirstInheritedVacuum
