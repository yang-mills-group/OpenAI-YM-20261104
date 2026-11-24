import YM.Integration.WilsonPhysicalThermalWickPrice
import YM.Integration.WilsonPhysicalThermalWickReturned

/-! On the two original sites a high-rank self-free factor and the ordinary
pair of unequal ranks have zero Maxwell response, at their actual placements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickFaces
open Finset Function Lattice Wilson RG Labels
open Next.Rank Next.Rank.Normal Next.Rank.Configuration
open WilsonPhysicalThermalWickPrice WilsonPhysicalThermalWickRescale
open scoped BigOperators Classical
variable {V:Type*}

theorem covers {P:ℝ}(one:1≤P)(q:Fin 2→ℕ)(ranks:q 0≤q 1)(S:Finset (Fin 2))(high:1∈S):
    P^(q 1-q 0)≤‖∏i∈S,(scales P i)^(q i)‖:=by
  have pp:=zero_lt_one.trans_le one
  by_cases low:(0:Fin 2)∈S
  · have all:S=univ:=by ext i;fin_cases i <;>simp [high,low]
    rw [all,Fin.prod_univ_two,norm_mul,norm_pow,norm_pow]
    simp [scales,abs_of_pos pp]
    rw [pow_sub₀ P pp.ne' ranks,mul_comm]
  · have only_high:S={1}:=by ext i;fin_cases i <;>simp [high,low]
    rw [only_high,prod_singleton,norm_pow]
    simp [scales,abs_of_pos pp]
    exact pow_le_pow_right₀ one (Nat.sub_le ..)

theorem zero (q:Fin 2→ℕ)(ranks:q 0<q 1)(p:Fin 2→poly V)(hp:∀i,pure (q i) (p i))
    (F:Symmetric (Fin 2 × V))(clear:∀i j:Fin 2 × V,i.1=j.1→F.cov i j=0)
    (S:Finset (Fin 2))(high:1∈S):
    blend F 0 (pot S p)=0:=by
  let a:=scales 2
  have mulone:a 0*a 1=1:=by norm_num [a,scales]
  have readzero:reads (edit (V:=V) a) 0=0:=by funext i;rw [mean];simp
  have same:=face a p q hp S F 0
  rw [invariant a mulone F clear,readzero] at same
  have bound:=covers (show (1:ℝ)≤2 by norm_num) q ranks.le S high
  have gt:(1:ℝ)<2^(q 1-q 0):=one_lt_pow₀ (by norm_num) (Nat.sub_pos_of_lt ranks).ne'
  by_contra nonunit
  have measure:=congrArg norm same
  rw [norm_mul] at measure
  exact (ne_of_lt (lt_mul_of_one_lt_left (norm_pos_iff.mpr nonunit) (gt.trans_le bound))) measure

end YM.Integration.WilsonPhysicalThermalWickFaces
end
