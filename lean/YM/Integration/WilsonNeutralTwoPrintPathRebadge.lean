import YM.Integration.WilsonNeutralTwoPrintPathPageSeason
import YM.Integration.WilsonReceivedCanonicalVerseRegister

/-! Each inherited connected insertion has one spatial root. Different inserted
blocks acquire distinct slots in the squarefree Gaussian conditional. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonNeutralTwoPrintPathRebadge
open Function Filter Finset Lattice RG Laurent Wilson
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos
open WilsonReceivedCompactVerseEntrance (CoverBill)
open IndependentSourcePathFamily (packOne)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}{e:ℕ}

def table (T:(i:I)→TowerS G (D i)):Outerm G D:=fun y S=>
  ∑i,packOne i (cn D i (T i) (y i)) S

theorem one (T:(i:I)→TowerS G (D i))(y:I → Cover)(i:I):
    table T y {i}=cn D i (T i) (y i):=by
  unfold table
  rw [Finset.sum_eq_single i]
  · simp [packOne]
  · intro j _ ne
    simp [packOne,ne]
  · simp

theorem dark (T:(i:I)→TowerS G (D i))(y:I → Cover)(S:Finset I)(away:∀i,S≠{i}):
    table T y S=0:=Finset.sum_eq_zero fun i _=>dif_neg (Ne.symm (away i))

theorem issued (T:(i:I)→TowerS G (D i))(grade:∀i,Auth (k i) (T i))
    {s A:ℝ}(hs:0 ≤ s)(hA:0 ≤ A)
    (funded:∀i a,a ≤ e → ∀r,Cork Bank.terrain 0 s A ((T i).2 a r)):
    Wellness k (table T) ∧ CoverBill (table T) e s A:=by
  constructor
  · refine ⟨fun y=>dark T y ∅ (by simp),?_,?_⟩
    · intro y S
      by_cases h:∃i,S={i}
      · obtain ⟨i,rfl⟩:=h
        rw [one,mass,Finset.sum_singleton]
        exact ((grade i).tuft _).shifted _
      · rw [dark T y S (fun i eqn=>h ⟨i,eqn⟩)]
        exact unstamped
    · intro y z S eqn
      by_cases h:∃i,S={i}
      · obtain ⟨i,rfl⟩:=h
        rw [one,one,eqn i (by simp)]
      · rw [dark T y S (fun i eqn=>h ⟨i,eqn⟩),dark T z S (fun i eqn=>h ⟨i,eqn⟩)]
  · intro y S a ha r
    by_cases h:∃i,S={i}
    · obtain ⟨i,rfl⟩:=h
      simpa only [one,Finset.card_singleton,pow_one] using Budges D i (T i) hs y (funded i a ha r)
    · rw [dark T y S (fun i eqn=>h ⟨i,eqn⟩)]
      exact Wig.zero.more (pow_nonneg hA _)

end YM.Integration.WilsonNeutralTwoPrintPathRebadge
end
