import YM.Integration.WilsonMeasuredPublicEntranceOwnerReading
import YM.Integration.WilsonMeasuredOwnerReserve
import YM.Integration.WilsonMeasuredPublicEntranceOpticalReserve

/-! The whole ordinary gallery and the single genuine marked owner are
funded together with one explicit change of radius. No occupied price is
lost under the true once-divided hard account. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOwnerWallet
open Function Lattice Wilson RG Source Labels Marker QuadraticLocal
open WilsonOriginalDepositedHard
open scoped Classical BigOperators
variable {G:Gauge} {V T I:Type} [DecidableEq V] [Fintype V] {J:Census V} {n:Side}
  (W:Rep G n) (o:V→Site n) (E:Lamps T I G W.p o J) (v:V)
  {d:ℕ} {F:Frame G d} (h:Coefficient F n) {A:Hol G} (fit:h.Format (o v) A W)
  {κ M k C:ℝ} (remn:h.remBound (o v) W κ M)
  (rent:Hard.Rent W.activities.forced W.activities.K W.p W.p.supportExponent k)
  (w:V→ℝ) (wp:∀j,0<w j) (hard:k≤κ/2) (regular:E.Paid w W.p.B W.p.supportExponent C)
local notation "quiet" => (Hard.rent rent : Hard T W.p W.activities.forced W.activities.K o J)
local notation "raised" => joined (quiet) v h fit (fun _ => (1:ℂ))
def divisor (w : V→ℝ) (v:V) (C M:ℝ) := max (max 1 C) (2*(w v*M))

include wp hard regular remn in
theorem original :
    let paid:=Stoop.radius w (divisor w v C M)
    (∀j,0<paid j) ∧ E.Paid paid W.p.B W.p.supportExponent 1 ∧
      (quiet).Paid paid W.p.B W.p.supportExponent κ ∧
      (raised).Paid paid W.p.B W.p.supportExponent κ := by
  intro paid
  let discount:=divisor w v C M
  have one:1≤discount:=(le_max_left ..).trans (le_max_left ..)
  have pos:0<discount:=zero_lt_one.trans_le one
  have fees:C≤discount:=(le_max_right ..).trans (le_max_left ..)
  have pp:∀j,0<paid j:=fun j=>div_pos (wp j) pos
  have reg:=Lamps.loan_monotone _ (Stoop.tighten w E wp one regular) ((inv_mul_le_one₀ pos).mpr fees)
  have booked:=WilsonMeasuredCompanionFace.fund rent v h fit (fun _:T=>1) E paid pp (fun _=>norm_one.le) remn reg
  have k0:=remn.choose_spec.choose_spec.2.2.2.1.le
  have budget:(paid v)*M≤(1/2:ℝ):=by
    change w v/discount*M≤_
    rw [div_mul_eq_mul_div,div_le_iff₀ pos]
    linarith only [show 2*(w v*M)≤discount from le_max_right ..]
  have bound:k+paid v*(κ*M)≤κ:=by nlinarith only [hard,mul_le_mul_of_nonneg_left budget k0]
  exact ⟨pp,reg,Hard.mono _ booked.1.2 (by linarith),Hard.mono _ booked.2.2 bound⟩

end YM.Integration.WilsonMeasuredPublicEntranceOwnerWallet
end
