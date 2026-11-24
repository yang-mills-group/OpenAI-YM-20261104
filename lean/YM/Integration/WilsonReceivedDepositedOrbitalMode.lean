import YM.Integration.WilsonReceivedDepositedOrbitalWick

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalMode
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open WilsonCoeffUV.Blue PowerSeries
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
open WilsonOriginalMixedGaussianTable (stock)
open scoped Classical BigOperators
variable {V U:Type}[Fintype V][DecidableEq V]
local notation "J" => Stock.census V

def face (s:Finset V):(J).Mode:=⟨s,Finset.mem_powerset.mpr (Finset.subset_univ _)⟩

theorem letters (w:V→ℂ)(s:Finset V):
    (∏j∈s,coefficient (J) (J).fire w j)=Poly.send (face s) (∏j∈s,w j):=by
  classical
  induction s using Finset.induction_on with
  | empty=>rw [Finset.prod_empty,Finset.prod_empty];rfl
  | @insert j s away ih=>
    rw [Finset.prod_insert away,Finset.prod_insert away,ih]
    have single:coefficient (J) (J).fire w j=Poly.send ((J).fire j) (w j):=by
      apply Marker.Poly.ext
      intro v
      by_cases rooted:v=(J).fire j <;> simp [coefficient,rooted]
    rw [single]
    apply YM.Multi.send_prod
    exact ⟨Finset.disjoint_singleton_left.mpr away,Finset.singleton_union j s⟩

theorem read (r:ℕ)(B:U→ℝ)(w:V→ℂ)(T:Finset V→Ink U)(s:Finset V)(d:ℕ)(kept:d≤r):
    (Order.observe (J) r (stock (J) r B (fun t:Finset V=>∏j∈t,coefficient (J) (J).fire w j) T) d).part
      (face s)=(∏u∈s,w u)*(MvPolynomial.eval B (coeff d (T s)):ℝ):=by
  unfold Order.observe
  rw [if_pos kept,Poly.part_smul]
  change ((d.factorial:ℂ)⁻¹)*(stock _ _ _ _ _).part (Join.pair (face s) (pick r d))=_
  rw [WilsonOriginalMixedGaussianTable.value,picked r kept]
  simp_rw [letters,Poly.part_send]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl]
    have nz:(d.factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero d
    field_simp
  · intro b _ ne
    have distinct:face s≠face b:=fun h=>ne (congrArg Subtype.val h).symm
    rw [if_neg distinct,zero_mul,zero_mul]
  · simp

end YM.Integration.WilsonReceivedDepositedOrbitalMode
end
