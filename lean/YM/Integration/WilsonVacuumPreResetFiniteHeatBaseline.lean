import YM.Integration.WilsonVacuumPreResetFiniteHeatIntake

/-! The existing folded-input award bounds the actual complete chart
polynomial before any signed change in its fine field. Its sole volume
factor restores the constant angular slot. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatBaseline
open Bloch Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G:Gauge}

theorem unpruced {α:Type}{n:Side}{r:ℕ}{P:Ten ℝ (Co n α) r}{A:ℝ}
    (positive:0 ≤ A)(book:∀x,|pruce P x| ≤ A)(x):|P x| ≤ (Fintype.card (Site n):ℝ)*A:=by
  let c:ℝ:=Fintype.card (Site n)
  have pos:0<c:=Nat.cast_pos.mpr Fintype.card_pos
  have great:1 ≤ c:=by dsimp [c];exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α:=Site n)))
  have v:=book x
  by_cases h:r=0
  · simp only [pruce,if_pos h,Pi.smul_apply,smul_eq_mul,abs_mul] at v
    change |c⁻¹| * |P x| ≤ A at v
    rw [abs_of_pos (inv_pos.mpr pos)] at v
    calc
      _=c*(c⁻¹*|P x|):=by rw [←mul_assoc,mul_inv_cancel₀ pos.ne',one_mul]
      _ ≤ _:=mul_le_mul_of_nonneg_left v pos.le
  · simpa only [pruce,if_neg h] using v.trans (le_mul_of_one_le_left positive great)

/-- All raw field components of the complete folded casePW have an
original before-side price. The exponent of the original invoice is fixed
before the stage, the mass of its finite receipt before any realization. -/
theorem original(G:Gauge)(e cap:ℕ):∃ d:ℕ,∀ C:Arch G,∃ A:ℝ,0 ≤ A ∧
    ∀ p:ScrollV e C,∀i ≤ e,∀r ≤ cap,∀x,
      |casePW p.wheel C.R p.cone p.W' i r x| ≤
        (Fintype.card (Site p.n):ℝ)*A*p.coin^d:=by
  classical
  let I:=Fin (e+1) × Fin (cap+1)
  have prices(z:I):=bankPrep G e z.1.val z.2.val (by omega)
  choose d issued using prices
  refine ⟨∑j:I,d j,fun C=>?_⟩
  choose s a s_pos a_pos delivery using fun z:I=>issued z C
  refine ⟨∑z:I,a z,Finset.sum_nonneg (fun z _=>a_pos z),?_⟩
  intro p i ij r rr x
  let z:I:=(⟨i,by omega⟩,⟨r,by omega⟩)
  have rate:=s_pos z
  have bank:=delivery z p
  have positive:0 ≤ a z*p.coin^(d z):=mul_nonneg (a_pos z) (pow_nonneg (zero_le_one.trans p.paid) _)
  have priced(y):|pruce (p.archCold i r) y| ≤ a z*p.coin^(d z):=by
    apply (show |pruce (p.archCold i r) y| ≤ a z*p.coin^(d z)*Real.exp (-(s z)*soar (tor p.n) y) from
      ((Real.norm_eq_abs _).ge.trans (bank.aim.2 y))).trans
    exact mul_le_of_le_one_right positive (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr rate.le) (Nat.cast_nonneg _)))
  have q:=unpruced positive priced ((C.roll p.n)∘x)
  have eq:p.archCold i r ((C.roll p.n) ∘x)=casePW p.wheel C.R p.cone p.W' i r x:=by
    simp [ScrollV.archCold,bend,turnTen,Function.comp_def]
  rw [eq] at q
  have aq:a z ≤ ∑j:I,a j:=Finset.single_le_sum (f:=a) (fun j _=>a_pos j) (mem_univ z)
  have dq:d z ≤ ∑j:I,d j:=Finset.single_le_sum (f:=d) (fun j _=>Nat.zero_le _) (mem_univ z)
  calc
    _ ≤ (Fintype.card (Site p.n):ℝ)*(a z*p.coin^(d z)):=q
    _ ≤ (Fintype.card (Site p.n):ℝ)*((∑j:I,a j)*p.coin^(∑j:I,d j)):=
      mul_le_mul_of_nonneg_left (mul_le_mul aq (pow_le_pow_right₀ p.paid dq)
        (pow_nonneg (zero_le_one.trans p.paid) _) (Finset.sum_nonneg (fun j _=>a_pos j))) (Nat.cast_nonneg _)
    _=_:=by ring

end YM.Integration.WilsonVacuumPreResetFiniteHeatBaseline
end
