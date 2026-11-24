import YM.Integration.WilsonThermometerWeakJointWidth

/-! One finite ordinary detector horizon pays the shared two-cell clearance
before choosing its actual three panels or either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakDisplacedHorizon
open Filter Set Lattice RG Push Next.Rank Next.Rank.Station MergeProof MergeProof.East
open PhysicalNext.Repeat.Legato Next.Rank.Tapes Next.Rank.Price
open scoped Classical Topology
open WilsonThermometerWeakJointWidth

theorem original (a:ℝ) (pos:0<a) (e d:ℕ):
    ∃H:ℕ,d≤H ∧ ∀(P:Fin 3→Panel H)(c:ℝ),Checks (P 0).arc (P 1).arc (P 2).arc c (trays H) H →
        power a (P 2).arc e<(P 0).arc:=by
  obtain ⟨v,hv⟩:=exists_nat_ge (4*(e:ℝ)+4*(a+5)+16)
  let H:=max d v
  refine ⟨H,le_max_left ..,?_⟩
  intro P c checks
  have large:4*(e:ℝ)+4*(a+5)+16≤H:=hv.trans (by exact_mod_cast (le_max_right d v))
  have count:1≤(trays H:ℝ):=by change 1≤((H+2:ℕ):ℝ);exact_mod_cast (by omega:1≤H+2)
  have hH:0≤(H:ℝ):=Nat.cast_nonneg H
  have spread:6≤(P 0).arc-(P 1).arc:=by linarith only [checks.boundA]
  have shift:6*H≤((P 0).arc-(P 1).arc)*H*(trays H):=by
    refine (mul_le_mul_of_nonneg_right spread hH).trans (le_mul_of_one_le_right ?_ count)
    exact mul_nonneg (le_trans (by norm_num) spread) hH
  have low:0≤(P 2).arc:=by linarith only [(P 2).huge,hH]
  unfold power
  rcases le_total (4*(a+5)) ((P 2).arc+5) with left|right
  · rw [max_eq_right left];linarith only [checks.boundB,checks.limitA,shift,large,pos]
  · rw [max_eq_left right];linarith only [checks.boundB,checks.limitA,shift,large,low,Nat.cast_nonneg (α:=ℝ) e]

end YM.Integration.WilsonThermometerWeakDisplacedHorizon
end
