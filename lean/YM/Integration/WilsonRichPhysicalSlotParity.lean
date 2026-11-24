import YM.Integration.WilsonRichPrimitiveInversion

/-! The full initially prescribed Wilson Wick register, with every descended
slot kept, has the original named slot parity at every coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRichPhysicalSlotParity
open Function Finset Lattice Wilson RG Labels PhysicalNext.Repeat.Legato
open MS MS.Menus MS.Theater MS.Local.Physical Pert PertExtension PertExtension.LatticePT
open FVAAlt2 FVA2 FormalOPE.RG10.InversionTop
open RegulatorIR.FVAAlt2.Lodge
open WilsonRichPrimitiveTerminal PowerSeries
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {B : Deck G}

theorem column (v : MS.Rake.Label B) (j : Lobby.JLit R.family.labels v)
    (bad : Odd (v.item.1+((R.family.labels.level v.h).grades j).2)) :
    Lobby.γ (basisR R) v j = 0 := by
  unfold Lobby.γ Shop.valueP
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : (R.family.labels.level v.h).grades i = (v.h,v.item.1.val)
  · have ho : Odd (((R.family.labels.level v.h).grades i).2+((R.family.labels.level v.h).grades j).2) := by
      simpa only [h] using bad
    rw [even_slot _ _ _ _ _ _ ho]
    simp
  · rw [Shop.cancel B i v.item.2 h,zero_mul]

variable {I : Type} [LinearOrder I] [Fintype I] (p : I → MS.Rake.Label B)
def named := ∑ i : I,(p i).item.1.val

theorem invoice (c : frames R p) (nonzero : charge R p c ≠ 0) :
    Even (named p + rank R p c) := by
  have each (i : I) : Even ((p i).item.1+((R.family.labels.level (p i).h).grades (c i)).2) := by
    refine Nat.not_odd_iff_even.mp (fun ho => nonzero ?_)
    have hz := (WilsonRichPrimitiveRows.price R (p i) (c i)).trans (column R (p i) (c i) ho)
    apply Finset.prod_eq_zero (mem_univ i)
    exact_mod_cast hz
  let f : I → ℕ := fun i => (p i).item.1+((R.family.labels.level (p i).h).grades (c i)).2
  have sumEven (l : Finset I) : Even (∑ i ∈ l,f i) := by
    induction l using Finset.induction_on with
    | empty => simp
    | insert i l hi ih => rw [sum_insert hi]; exact (each i).add ih
  simpa only [f,sum_add_distrib,named,rank] using sumEven univ

variable {n : Side} (x : I → Site n) (ev : Even n.val)
include ev

/-- All orders in the independent normalized finite register. No common
unrestored degree or cancellation of separate first-order marks is assumed. -/
theorem closed_price (k : ℕ) (hk : Odd (k+named p)) :
    coeff k (closed R p x) = 0 := by
  simp only [closed,map_sum,coeff_C_mul,coeff_mk]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases zero : charge R p c = 0
  · simp [zero]
  have he := Nat.even_iff.mp (invoice R p c zero)
  have ho := Nat.odd_iff.mp hk
  have z : Odd (k+rank R p c) := Nat.odd_iff.mpr (by omega)
  have vanish : Fixed.treeMom R.metals.O (∏ i, gauge R p x c i) (rank R p c) k = 0 :=
    Orb.normalized_odd R.alloy.B.ratio ev _ z
  rw [vanish,Complex.ofReal_zero,mul_zero]

theorem original (k : ℕ) (hk : Odd (k+named p)) :
    coeff k (Lobby.WilsonPoint R.metals.O (basisR R) n x p) = 0 := by
  rw [← terminal R p x]
  exact closed_price R p x ev k hk

end YM.Integration.WilsonRichPhysicalSlotParity
