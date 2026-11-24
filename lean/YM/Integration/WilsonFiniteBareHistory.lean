import YM.Integration.WilsonFiniteIncomingMarkedWinding
import YM.WilsonCoeffUV.Reclosure.Paths.RetainBase

/-! The independently computed finite vacuum starts at the exact periodization
of the four-link Wilson plaquette. The first block therefore has the covered
program's pre-reset winding income and the same measured formal reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteBareHistory
open Function Filter Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Winding
open scoped Classical

variable {G : Gauge} {e i r : ℕ} {E : Credit}

theorem top (A : Levels G) (β : ChartRatio G) (N : ℕ) :
    (story A β N N).1 = emera (actionW A β N N) := by
  rw [actionW,story_top]
  funext n k l
  cases l with
  | zero => rfl
  | succ l => exact moon_wrap G k l n

theorem income (Q : Realm G (e+1) E) {m : ℕ} (hm : Q.anchor ≤ m) {s : ℝ} (hs : 0 < s) :
    ∃ V : ℝ, 1 ≤ V ∧ ∀ (n : Side) (k : ℕ), k ≤ e → ∀ l,
      Sight ((story Q.draws Q.paid (m+1) (m+1)).1 (n*(loose Q.draws m).L) k l)
        (actionW Q.draws Q.paid (m+1) (m+1) k l) (holt Q m hm s hs).s V := by
  let base := cloVent Q m (m+1) (loose Q.draws m).L hm (Nat.lt_succ_self m) s hs
  refine ⟨base.coin,base.paid,?_⟩
  intro n k hk l
  rw [top]
  exact (cloVent Q m (m+1) n hm (Nat.lt_succ_self m) s hs).fare k hk l

theorem rebase (A : Levels G) (β : ChartRatio G) (m : ℕ) (n : Side) :
    (story A β (m+1) m).1 n =
      Blue.mix (back (Kstar (freshet A β (m+1) m))) (lop (coil0 A β m (m+1) n)) := by
  rw [story_stride A β (Nat.lt_succ_self m)]
  change Blue.mix _ (lop (unripe A β (m+1) m (story A β (m+1) (m+1)).1 n)) = _
  rw [top]
  rfl

theorem first (hi : i ≤ e) (H E : Credit) (u : Gear G → ℝ) (hu : ∀ I, 0 < u I) :
    ∃ (s c : Gear G → ℝ) (U : Credit), (∀ I, 0 < s I ∧ (s I)⁻¹ ≤ c I) ∧
      ∀ (Q : Realm G (e+1) E) (m : ℕ) (n : Side) (hm : Q.anchor ≤ m),
        let I := (Q.mint m hm).gear
        c I ≤ Q.cash H m →
        Sight (unripe Q.draws Q.paid (m+1) m (story Q.draws Q.paid (m+1) (m+1)).1 n i r)
          (freshet Q.draws Q.paid (m+1) m i r) (s I) (Q.cash U m) := by
  obtain ⟨s,c,U,tariff,step⟩ := purchaseW G e i r hi H E u hu
  refine ⟨s,c,U,tariff,?_⟩
  intro Q m n hm I charge
  rw [top]
  exact step Q m (m+1) n hm (Nat.lt_succ_self m) charge

end YM.Integration.WilsonFiniteBareHistory
