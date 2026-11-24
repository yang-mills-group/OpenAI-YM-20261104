import YM.Integration.WilsonIndependentCollarPointBill

/-! The external Laurent and engineering charge of the actual finite trial
is attached to each occupied name once and is independent of Taylor order. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOriginalDose
open Function Finset Lattice Laurent Wilson RG Source Labels
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords WilsonReceivedCanonicalVerseBasis
open WilsonReceivedCanonicalVerseRegister PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} (R:Run G)(k:I→ℕ)

def weight (N p K:ℕ)(v:(j:I)→R.family.label (k j))(j:I)(c:Choice R k j)(g size:ℝ):ℝ:=
  ‖dose R k N p K v j c‖*(g⁻¹)^(pole R k (entry R k j c))*size^(k j)

def axisFee (v:(j:I)→R.family.label (k j))(j:I):ℝ:=
  ∑c:Choice R k j, shoulder R k j c*(R.family.labels.level (k j)).coeffSize (v j)

theorem original (N p K:ℕ)(top:K≤N)(v:(j:I)→R.family.label (k j))(j:I)(g size:ℝ)
    (positive:0<g)(small:g≤1)(span:0 ≤ size):
    ∑c:Choice R k j, weight R k N p K v j c g size ≤ axisFee R k v j*(size/g)^(k j):=by
  unfold axisFee;rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  have actual:=WilsonReceivedCanonicalVerseRegister.measured R k N p K top v j c
  have debit:=WilsonOriginalStarGradedScene.pole_grade R k (entry R k j c)
  rw [site] at debit
  have one:1≤g⁻¹:=(one_le_inv₀ positive).2 small
  have step: (g⁻¹)^(pole R k (entry R k j c))≤(g⁻¹)^(k j):=pow_le_pow_right₀ one debit
  calc
    _ ≤ (shoulder R k j c*(R.family.labels.level (k j)).coeffSize (v j))*(g⁻¹)^(k j)*size^(k j):=
      mul_le_mul_of_nonneg_right (mul_le_mul actual step (pow_nonneg (inv_nonneg.mpr positive.le) _) ((norm_nonneg _).trans actual)) (pow_nonneg span _)
    _ = _:=by rw [div_eq_mul_inv,mul_pow];ring

theorem family [DecidableEq I](N p K:ℕ)(top:K≤N)(v:(j:I)→R.family.label (k j))(S:Finset I)(g size:ℝ)
    (positive:0<g)(small:g≤1)(span:0 ≤ size):
    (∑q:(j:S)→Choice R k j,∏j:S,weight R k N p K v j (q j) g size) ≤
      ∏j:S,(axisFee R k v j*(size/g)^(k j)):=by
  have all:(∑q:(j:S)→Choice R k j,∏j:S,weight R k N p K v j (q j) g size)=
      ∏j:S,∑c:Choice R k j, weight R k N p K v j c g size:=by symm;exact Fintype.prod_sum ..
  rw [all]
  apply Finset.prod_le_prod
  · exact fun j _=>Finset.sum_nonneg fun c _=>mul_nonneg (mul_nonneg (norm_nonneg _)
      (pow_nonneg (inv_nonneg.mpr positive.le) _)) (pow_nonneg span _)
  · exact fun j _=>original R k N p K top v j g size positive small span

end YM.Integration.WilsonIndependentCollarOriginalDose
end
