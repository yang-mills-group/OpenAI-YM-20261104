import YM.Integration.WilsonThermometerRegisteredWindow
import YM.Integration.WilsonOriginalThermometerRefund
import YM.Integration.WilsonMovingMentorPageCoupling
import YM.Integration.WilsonReceivedCloseOrdinaryGrade
import YM.Integration.WilsonVacuumPreResetSameTime

/-! Restore the two real source weights at the station, including every proper partition. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredRent

open Filter Finset Lattice RG Tree Marker QuadraticLocal QuadraticLocal.Advent Org AllOrder AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard RemainderComparison
open ConnectedActivityE6 Multi Pert.Asymptotics
open WilsonThermometerRegisteredWindow
open scoped Classical BigOperators

local notation "J" => Stock.census (Fin 3)

def grade (p:ℕ) := p+161
def degree (p:ℕ) := p+159
def fraction (p:ℕ) : ℝ := ((3:ℝ)^(grade p)+10)⁻¹
def invoice (p:ℕ) : ℝ := WilsonReceivedCloseOrdinaryGrade.invoice (J) 2 79 p 1
theorem positive (p:ℕ) : 0 < fraction p := by unfold fraction;positivity

private theorem tariff {E g:ℝ} (gp:0 < g) (s:(J).Mode) (p:ℕ)
    (two:s.val.card=2) (w:ℝ) (roof:g^157 ≤ w) (cold:g ≤ 1)
    (e0:0 ≤ E) (paid:E ≤ g^(grade p)) :
    (w⁻¹)*bill s g E (degree p) ≤ invoice p*g^(p+1) := by
  have cap: (w⁻¹) ≤ ((1:ℝ)*(g⁻¹)^79)^s.val.card:=by
    rw [two,one_mul,←pow_mul,inv_pow]
    exact (inv_le_inv₀ (lt_of_lt_of_le (pow_pos gp 157) roof) (pow_pos gp _)).2
      ((pow_le_pow_of_le_one gp.le cold (by decide : 157 ≤ 79*2)).trans roof)
  apply WilsonReceivedCloseOrdinaryGrade.earned (J) s 2 79 p le_rfl gp cold gp
    (by linarith) (by linarith only [inv_pos.mpr gp]) two.le
  apply mul_le_mul cap _ ?_ (by positivity)
  · unfold bill
    refine add_le_add ?_ le_rfl
    refine Finset.sum_le_sum fun block _ => ?_
    apply mul_le_mul (mul_le_mul_of_nonneg_left paid (Nat.cast_nonneg _)) ?_ ?_ (by positivity)
    · exact pow_le_pow_left₀ (add_nonneg (inv_nonneg.mpr gp.le) e0) (add_le_add le_rfl paid) _
    · exact pow_nonneg (add_nonneg (inv_nonneg.mpr gp.le) e0) _
  · unfold bill
    exact add_nonneg (sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) e0) (pow_nonneg (add_nonneg (inv_nonneg.mpr gp.le) e0) _)) (mul_nonneg (pow_nonneg gp.le _) (Nat.cast_nonneg _))

variable {G:Gauge} (R:Run G) (simple:G.Simple)
def opening (p seats:ℕ) : ℕ := max
  (eventually_atTop.mp (WilsonVacuumPreResetSameTime.ratios R simple)).choose
  (max (eventually_atTop.mp (WilsonOriginalThermometerRefund.measured R simple)).choose
    (eventually_atTop.mp (WilsonMovingMentorPageCoupling.repaid R simple seats (grade p)
      (ε:=1) zero_lt_one)).choose)

/-- On the two-date physical course these two displayed receipts are part of the same
centered report. The activation and the raw order depend only on the original slot count
and the requested accuracy. -/
theorem original (p seats ord:ℕ) {i per:ℕ} (activated:opening R simple p seats ≤ i)
    (ready:grade p ≤ ord)
    (s:(J).Mode) (two:s.val.card=2) {rent weight wage value mark:ℝ}
    (salary:1 ≤ wage) (nonneg:0 ≤ rent)
    (refund:(8*wage^seats)*rent ≤ fraction p*(Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta)^(grade p+1))
    (roof:(Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta)^157 ≤ weight) :
    let g:=Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
    let h:=regulatorRun R.family (i+2) per i
    let E:=fraction p*h^(grade p)+fraction p*g^ord+fraction p*g^(grade p)
    let E':=(8*(budgetR R i)^seats)*rent+fraction p*g^(grade p)
    weight*value ≤ bill s g E (degree p)+bill s g E' (degree p)+weight*(mark*g^(p+1)) →
      value ≤ (2*invoice p+mark)*g^(p+1) := by
  intro g h E E' paid
  let q:=grade p
  let B:=budgetR R i
  have old:h ≤ 3*g:=(eventually_atTop.mp (WilsonVacuumPreResetSameTime.ratios R simple)).choose_spec
    i ((le_max_left ..).trans activated) (i+2) per (by omega)
  obtain ⟨gp,cold,_,_⟩:=(eventually_atTop.mp (WilsonOriginalThermometerRefund.measured R simple)).choose_spec
    i ((le_max_left ..).trans ((le_max_right ..).trans activated)) per
  have b0:0 ≤ B:=by
    exact le_min (Real.exp_pos _).le (Real.rpow_nonneg
      (zero_le_one.trans (R.alloy.B.a.fits.delayed (i+1)).le) _)
  have purchase:B^seats*g^(q+1) ≤ g^q:=by
    simpa only [one_mul] using (eventually_atTop.mp (WilsonMovingMentorPageCoupling.repaid R simple
      seats q (ε:=1) zero_lt_one)).choose_spec i ((le_max_right ..).trans ((le_max_right ..).trans activated))
        B b0 (min_le_right ..) (i+2) per (by omega)
  have wp:0 < weight:=(pow_pos gp 157).trans_le roof
  have ε0:0<fraction p:=positive p
  have hc:0 ≤ h:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have qq:0 ≤ g^q:=pow_nonneg gp.le _
  have top:rent ≤ fraction p*g^(q+1):=
    (le_mul_of_one_le_left nonneg (by have:=one_le_pow₀ salary (n:=seats);linarith)).trans refund
  have height:h^q ≤ (3:ℝ)^q*g^q:=by simpa only [mul_pow] using pow_le_pow_left₀ hc old q
  have first:E ≤ g^q:=calc
    _ ≤ fraction p*((3:ℝ)^q*g^q)+fraction p*g^q+fraction p*g^q:=by
      dsimp only [E]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left height ε0.le)
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le cold ready) ε0.le)) le_rfl
    _ = fraction p*((3:ℝ)^q+2)*g^q:=by ring
    _ ≤ 1*g^q:=by
      apply mul_le_mul_of_nonneg_right _ qq
      rw [fraction]
      rw [inv_mul_le_iff₀ (by positivity)]
      dsimp only [q]
      linarith
    _ = _:=one_mul _
  have second:E' ≤ g^q:=calc
    _ ≤ (8*B^seats)*(fraction p*g^(q+1))+fraction p*g^q:=by
      exact add_le_add (mul_le_mul_of_nonneg_left top (by positivity)) le_rfl
    _ = 8*fraction p*(B^seats*g^(q+1))+fraction p*g^q:=by ring
    _ ≤ 8*fraction p*g^q+fraction p*g^q:=by gcongr
    _ = fraction p*9*g^q:=by ring
    _ ≤ 1*g^q:=by
      apply mul_le_mul_of_nonneg_right _ qq
      rw [fraction,inv_mul_le_iff₀ (by positivity)]
      have three:0 ≤ (3:ℝ)^grade p:=by positivity
      linarith
    _ = _:=one_mul _
  have e0:0 ≤ E:=add_nonneg (add_nonneg (mul_nonneg ε0.le (pow_nonneg hc _)) (mul_nonneg ε0.le (pow_nonneg gp.le _))) (mul_nonneg ε0.le qq)
  have e'0:0 ≤ E':=add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg b0 _)) nonneg) (mul_nonneg ε0.le qq)
  have one:=tariff gp s p two weight roof cold e0 first
  have two':=tariff gp s p two weight roof cold e'0 second
  calc
    value = weight⁻¹*(weight*value):=by field_simp
    _ ≤ weight⁻¹*(bill s g E (degree p)+bill s g E' (degree p)+weight*(mark*g^(p+1))):=
      mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr wp.le)
    _ = weight⁻¹*bill s g E (degree p)+weight⁻¹*bill s g E' (degree p)+mark*g^(p+1):=by
      rw [mul_add,mul_add,←mul_assoc,inv_mul_cancel₀ wp.ne',one_mul]
    _ ≤ invoice p*g^(p+1)+invoice p*g^(p+1)+mark*g^(p+1):=
      add_le_add (add_le_add one two') le_rfl
    _ = _:=by ring

end YM.Integration.WilsonThermometerRegisteredRent
