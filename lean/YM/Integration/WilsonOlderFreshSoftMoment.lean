import YM.Integration.WilsonOlderFreshSoftTrialSize

/-! The actual finite Laurent superposition of all planted coordinates, before its absolute moment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftMoment
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos PhysicalNext.Repeat.Legato OriginalMarkedSourceComet
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[Fintype ι][LinearOrder ι]
variable (R:Run G)(D d:ι→ℕ)
local notation "F" i:max=>R.family.labels.level (d i)


open WilsonCoeffUV.Shard


open WilsonOlderFreshSoftFigureSize (ink gross)
def mixed (g:ℝ)(x:∀i,(F i).Coeff)(P:(∀i,(F i).Index)→Era G ℝ)(q r:ℕ):=
  fun z=>∑b,WilsonOriginalPublicTrialFigure.weight R d g x b*((P b).2 q r z:ℂ)

theorem original (g:ℝ)(x:∀i,(F i).Coeff)(P:(∀i,(F i).Index)→Era G ℝ)(q r:ℕ)
    (source:∀b,Summable (fun z=>‖(P b).2 q r z‖)):
    SumBudget (fun z=>‖mixed R d g x P q r z‖) (gross R d g x P q r):=by
  let f:=fun b z=>‖WilsonOriginalPublicTrialFigure.weight R d g x b‖*‖(P b).2 q r z‖
  have income (b):Summable (f b):=(source b).mul_left _
  have total:Summable fun z=>∑b,f b z:=summable_sum fun b _=>income b
  have bounded (z):‖mixed R d g x P q r z‖≤∑b,f b z:=by
    unfold mixed
    apply (norm_sum_le ..).trans
    exact sum_le_sum fun b _=>by simp only [f,norm_mul,Complex.norm_real,le_refl]
  have absolute:=total.of_nonneg_of_le (fun z=>norm_nonneg _) bounded
  refine ⟨fun _=>norm_nonneg _,absolute,(absolute.tsum_le_tsum bounded total).trans_eq ?_⟩
  rw [Summable.tsum_finsetSum (fun b _=>income b)]
  apply sum_congr rfl
  intro b _
  exact tsum_mul_left

/-- The rank-zero entry is included once; restricting the second range to positive ranks
gives the same upper wage for the entire nonconstant tensor. -/
theorem ranks (g:ℝ)(x:∀i,(F i).Coeff)(P:(∀i,(F i).Index)→Era G ℝ)
    (h e:ℕ)(pay C:ℝ)(pos:0≤pay)(C0:0≤C)
    (income:∀q≤e,∀r:ℕ,(∀b,Summable (fun z=>‖(P b).2 q r z‖)) ∧
      pay*gross R d g x P q r≤C):
    ∀(Q:Finset ℕ),(∀q∈Q,q≤e) → ∀(ranks:ℕ→Finset ℕ),(∀q∈Q,(ranks q).card≤h+e+1) →
      ∑q∈Q,∑r∈ranks q,pay*(∑'z,‖mixed R d g x P q r z‖)≤(Q.card:ℝ)*(h+e+1:ℕ)*C:=by
  intro Q through ranks count
  calc
    _ ≤ ∑q∈Q,∑r∈ranks q,C:=sum_le_sum fun q hq=>sum_le_sum fun r _=>
      let p:=income q (through q hq) r
      (mul_le_mul_of_nonneg_left (original R d g x P q r p.1).2.2 pos).trans p.2
    _ ≤ ∑q∈Q,((h+e+1:ℕ):ℝ)*C:=sum_le_sum fun q hq=>by
      rw [sum_const,nsmul_eq_mul];gcongr;exact count q hq
    _ = _ :=by rw [sum_const,nsmul_eq_mul,mul_assoc]

end YM.Integration.WilsonOlderFreshSoftMoment
end
