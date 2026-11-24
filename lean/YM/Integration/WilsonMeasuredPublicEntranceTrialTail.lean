import YM.Integration.WilsonMeasuredPublicEntranceGridCompensation

/-! The real trial pays its full signed owner under a bounded K-born
observable. Consequently its finite crop remainder is affordable on every
older held Wilson field, including both flat reports. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTrialTail
open Function Lattice Wilson RG Source Labels PhysicalNext.Repeat Legato
open WilsonMeasuredPublicEntranceCheapOrder WilsonMeasuredCoefficientTransport
open WilsonThermometerUnitFilingFieldRange WilsonOriginalAlternativeHearing
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p f d : ℕ} (cut : f≤N)
    (W : Rep G (R.family.side f p)) (same : W.eval=(R.family.path.rep N p f).eval)
    (o : Site (R.family.side f p)) (q : Coefficient (R.family.labels.level d) (R.family.side f p))
    {κ M C : ℝ} (fee : q.remBound o W κ M)
    (trial : Config G (R.family.side f p)→ℂ)
    (read : ∀U,q.density o (R.family.localSection d) W U=W.eval U • trial U)
    (cap : ∀U, ‖trial U‖≤C)
local notation "P" => R.family.path.rep N p f
local notation "tariff" => C+(cost G d W.p.threshold*(R.family.labels.level d).coeffSize q.x+M)

include same cut fee read cap in
theorem owner (U : Config G (R.family.side f p)) :
    ‖((P).eval U)⁻¹ • account q W U‖ ≤ tariff := by
  have cash := point R d W q o fee U
  have pos : ((P).eval U:ℂ)≠0 := by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson cut U).ne'
  have eq := read U
  change (W.eval U:ℂ)*q.exponentialEntry o (R.family.localSection d) W U+account q W U=_ at eq
  simp only [Complex.real_smul,same] at eq
  have disp : ((P).eval U)⁻¹ • account q W U =
      trial U-q.exponentialEntry o (R.family.localSection d) W U := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    apply mul_left_cancel₀ pos
    rw [←mul_assoc,mul_inv_cancel₀ pos,one_mul]
    linear_combination eq
  rw [disp]
  exact (norm_sub_le ..).trans (add_le_add (cap U) cash)

theorem product {V : Type*} (x y : V→ℂ) (n δ : V→ℝ) (px : ∀v,‖x v‖≤n v)
    (small : ∀v,‖x v-y v‖≤δ v) (vs : List V) :
    ‖(vs.map x).prod-(vs.map y).prod‖ ≤ route n (fun v=>n v+δ v) δ vs := by
  have eq := crossed (1:ℂ) x y (fun v=>x v-y v) (fun _=>one_mul _) vs
  rw [one_mul] at eq
  rw [eq]
  simpa only [sub_sub_cancel] using price x (fun v=>x v-y v) n δ px small vs

include same cut fee read cap in
theorem heard {V : Type*} (vs : List V)
    (x y : Config G (R.family.side f p)→V→ℂ) (n δ : V→ℝ)
    (px : ∀U v,‖x U v‖≤n v) (small : ∀U v,‖x U v-y U v‖≤δ v) {m : ℕ} (down : m≤f)
    (T : Config G (R.family.side m p)) :
    ‖held R.family N p (fun U=>account q W U*((vs.map (x U)).prod-(vs.map (y U)).prod)) down T‖ ≤
      tariff*route n (fun v=>n v+δ v) δ vs := by
  rw [normalized R.family N p R.makes cut _ down]
  apply actualTransport_norm_le R.family R.makes cut _ down
  intro U
  rw [←smul_mul_assoc,norm_mul]
  have first := owner R cut W same o q fee trial read cap U
  exact mul_le_mul first (product (x U) (y U) n δ (px U) (small U) vs) (norm_nonneg _)
    ((norm_nonneg _).trans first)

end YM.Integration.WilsonMeasuredPublicEntranceTrialTail
end
