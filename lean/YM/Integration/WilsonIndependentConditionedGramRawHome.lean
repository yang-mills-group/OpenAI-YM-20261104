import YM.Integration.WilsonIndependentConditionedBankRawUnits

/-! Unprojected physical home on its own registered station and reporter.
The factor `fixed` uses only the raw frame. -/
set_option warningAsError true
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramRawHome
open Function Finset Lattice RG Wilson Source Labels Extra.Histories Motion
open WilsonIndependentConditionedBankRawUnits (home)
open scoped Classical BigOperators
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

def fixed (d:ℕ):ℝ:=
  let Φ:=R.family.labels.level d
  4*(2:ℝ)^(Finset.univ.sup fun i:Φ.Index=>(Φ.grades i).2)*orbitCost Φ

theorem fixed_nonnegative (d:ℕ):0 ≤ fixed R d:=by
  have orbit:0 ≤ orbitCost (R.family.labels.level d):=zero_le_one.trans (orbitCost_one_le _)
  unfold fixed
  positivity

theorem nonnegative (d j f:ℕ)(η:ℝ)(t:ℂ){w:ℝ}(nn:0 ≤ w):0 ≤ home R d j f η t w:=by
  have F:=fixed_nonnegative R d
  have P:=Real.rpow_nonneg (div_nonneg (R.family.S.a_pos j).le (R.family.S.a_pos f).le) ((d:ℝ)+η)
  calc
    _ ≤ fixed R d*(‖t‖*w)*(a j/a f)^((d:ℝ)+η):=mul_nonneg (mul_nonneg F (mul_nonneg (norm_nonneg _) nn)) P
    _=home R d j f η t w:=by unfold home fixed;ring

theorem leaf {j f d U E:ℕ}{t:ℂ}{M w η:ℝ}
    (mark:‖t‖ ≤ 1)(nn:0 ≤ w)(fee:w ≤ M*(β f)^E)
    (reach:a j/a f ≤ (β f)^U)(start:0 ≤ η)(small:η ≤ 1):
    home R d j f η t w ≤ M*fixed R d*(β f)^(E+U*(d+1)):=by
  have one:1 ≤ β f:=(R.family.path.levels.fits.delayed f).le
  have ratio:0 ≤ a j/a f:=(div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)).le
  have bounded:(a j/a f)^((d:ℝ)+η) ≤ ((β f)^U)^(d+1):=calc
    _ ≤ ((β f)^U)^((d:ℝ)+η):=Real.rpow_le_rpow ratio reach (by positivity)
    _ ≤ ((β f)^U)^((d+1:ℕ):ℝ):=Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ one) (by push_cast;linarith)
    _=_:=Real.rpow_natCast ..
  have scaled:‖t‖*w ≤ M*(β f)^E:=(mul_le_of_le_one_left nn mark).trans fee
  calc
    _=fixed R d*(‖t‖*w*(a j/a f)^((d:ℝ)+η)):=by unfold home fixed;ring
    _ ≤ fixed R d*(M*(β f)^E*((β f)^U)^(d+1)):=mul_le_mul_of_nonneg_left
      (mul_le_mul scaled bounded (Real.rpow_nonneg ratio _) (nn.trans fee)) (fixed_nonnegative R d)
    _=_:=by rw [pow_add (β f) E (U*(d+1)),pow_mul (β f) U (d+1)];ring

theorem charged {j f d E:ℕ}{t:ℂ}{M w η:ℝ}
    (mark:‖t‖ ≤ 1)(nn:0 ≤ w)(date:j ≤ f)(small:η ≤ 1)
    (paid:2*(a j/a f)^(d+1)*w ≤ M*(β f)^E):
    home R d j f η t w ≤ M*fixed R d*(β f)^E:=by
  have ratio:1 ≤ a j/a f:=(one_le_div (R.family.S.a_pos f)).2 (R.family.S.strictAnti.antitone date)
  have convert:(a j/a f)^((d:ℝ)+η) ≤ (a j/a f)^(d+1):=calc
    _ ≤ (a j/a f)^((d+1:ℕ):ℝ):=Real.rpow_le_rpow_of_exponent_le ratio (by push_cast;linarith)
    _=_:=Real.rpow_natCast ..
  have owned:=mul_le_mul (mul_le_of_le_one_left nn mark) convert
    (Real.rpow_nonneg (zero_le_one.trans ratio) _) nn
  have half: w*(a j/a f)^(d+1) ≤ 2*(a j/a f)^(d+1)*w:=by
    linarith only [mul_nonneg nn (pow_nonneg (zero_le_one.trans ratio) (d+1))]
  calc
    _=fixed R d*(‖t‖*w*(a j/a f)^((d:ℝ)+η)):=by unfold home fixed;ring
    _ ≤ fixed R d*(M*(β f)^E):=mul_le_mul_of_nonneg_left (owned.trans (half.trans paid)) (fixed_nonnegative R d)
    _=_:=by ring

theorem face {I:Type}{f:ℕ}(s:Finset I)(E:I→ℕ)(h U c:I→ℝ)
    (source:∀i,0 ≤ h i)(colour:∀i,0 ≤ c i)(priced:∀i,h i ≤ U i*(β f)^(E i)):
    (∏i∈s,(1+h i*c i)) ≤ (∏i∈s,(1+U i*c i))*(β f)^(∑i∈s,E i):=by
  classical
  have one:1 ≤ β f:=(R.family.path.levels.fits.delayed f).le
  refine (Finset.prod_le_prod (fun i _=>add_nonneg zero_le_one (mul_nonneg (source i) (colour i)))
    (fun i _=>show 1+h i*c i ≤ (1+U i*c i)*(β f)^(E i) from ?_)).trans_eq ?_
  · calc
      _ ≤ (β f)^(E i)+(U i*(β f)^(E i))*c i:=
        add_le_add (one_le_pow₀ one) (mul_le_mul_of_nonneg_right (priced i) (colour i))
      _=_:=by ring
  · rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

end YM.Integration.WilsonIndependentConditionedGramRawHome
