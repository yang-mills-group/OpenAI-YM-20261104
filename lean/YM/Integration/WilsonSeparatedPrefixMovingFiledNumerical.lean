import YM.Integration.WilsonSeparatedPrefixMovingMeasuredContrast
import YM.Integration.WilsonIndependentFittedRosterCash

/-! Numerical product restoration on the already signed, common-exterior
defect. A full coefficient reserve is spent only in the discarded grades. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingFiledNumerical
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt positive)
open WilsonIndependentFittedRosterCash (reserve numerical)
open WilsonIndependentFittedNumericalProduct (signed added)
open PowerSeries Finset
open scoped BigOperators Classical
variable {I:Type}[Fintype I]{J:I → Type}[∀i,Fintype (J i)]
local notation "Film" => PowerSeries ℂ
local notation "RealFilm" => PowerSeries ℝ

theorem one (e:ℕ)(g:ℝ)(small:|g| ≤ 1)(s:Film)(P:I → Film)(Δ:Film):
    ‖cash e g ((s*∏i,P i)*Δ)-(cash e g s*(∏i,cash e g (P i)))*cash e g Δ‖ ≤
      ((Fintype.card I:ℝ)+2)*|g|^(e+1)*belt e s*(∏i,belt e (P i))*belt e Δ:=by
  let f:Option (Option I) → Film:=fun t=>t.elim s (fun j=>j.elim Δ P)
  have ticket:=signed e small univ f
  simp only [Fintype.prod_option,f,Option.elim_none,Option.elim_some,card_univ,Fintype.card_option,
    Nat.cast_add,Nat.cast_one] at ticket
  calc
    _=‖cash e g (s*(Δ*∏i,P i))-cash e g s*(cash e g Δ*∏i,cash e g (P i))‖:=by congr 2 <;> ring
    _=‖cash e g s*(cash e g Δ*∏i,cash e g (P i))-cash e g (s*(Δ*∏i,P i))‖:=norm_sub_rev ..
    _≤_:=ticket.trans_eq (by ring)

theorem paid (e:ℕ)(g:ℝ)(small:|g| ≤ 1)(s:Film)(A:∀i,J i → RealFilm)(Δ:((i:I) → J i) → RealFilm)
    (M:ℝ)(wage:∀a,belt e (embed (Δ a)) ≤ M):
    ‖cash e g (∑a,(s*embed (∏i,A i (a i)))*embed (Δ a))-
       cash e g s*(∑a,(∏i,cash e g (embed (A i (a i))))*cash e g (embed (Δ a)))‖ ≤
       ((Fintype.card I:ℝ)+2)*|g|^(e+1)*belt e s*reserve e A*M:=by
  rw [added,Finset.mul_sum,←Finset.sum_sub_distrib]
  unfold reserve;rw [Fintype.prod_sum,Finset.mul_sum,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
  intro a _
  rw [map_prod,←mul_assoc (cash e g s)]
  have signFee:=positive e s
  have pinFee:=Finset.prod_nonneg (s:=Finset.univ) (fun i _=>positive e (embed (A i (a i))))
  exact (one e g small s (fun i=>embed (A i (a i))) (embed (Δ a))).trans
    (mul_le_mul_of_nonneg_left (wage a) (by positivity))

end YM.Integration.WilsonSeparatedPrefixMovingFiledNumerical
end
