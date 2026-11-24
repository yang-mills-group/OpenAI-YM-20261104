import YM.Integration.WilsonPositionProgramAngularArm
import YM.Integration.WilsonPositionProgramFiniteRootEnvelope
import YM.Integration.WilsonPositionProgramReceivedRecastDrivers
import YM.Integration.WilsonPositionProgramRecastInputInvoice

/-! Numerical grade and radius books for the physical finite dates prior to taking either limit. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramDatedDrivers
open Finset Function Filter MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise AllOrder AllOrder.Floe
open AllOrder.Floe.Step Next.SectorChange Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants PertExtension.Series
open WilsonPositionProgramFiledGaussianChange WilsonPositionProgramHeatedWallet WilsonPositionProgramFiniteRootEnvelope
open scoped Classical BigOperators
variable {V X ι:Type}[DecidableEq V][Fintype V]{G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{path:PathData G}{O:ChartRatio G}
  {P:Passport f V}{R:Census V}{r:ℕ}

def length (grades:V→ℕ)(i:Hot (Board R r)):ℕ:=Launch.index R grades (Join.left i.val)+1+(Join.right i.val).val.card

def gain (G:Gauge)(grades:V→ℕ)(v:ℕ)(i:Hot (Board R r)):ℝ:=
  (((Join.right i.val).val.card.factorial:ℕ):ℝ)*|2*(2*WilsonPositionProgramCurvedAngularPrice.price G (length grades i) v+1)|

def salary (G:Gauge)(grades:V→ℕ)(σ:ℝ)(order shelf:ℕ)(i:Hot (Board R r)):ℝ:=
  gain G grades (order+shelf+1) i * (WilsonReceivedSourceCoefficientIncome.price G σ 1 order shelf*Fintype.card V)

def movement (G:Gauge)(grades:V→ℕ)(v:ℕ)(probes:R.Mode→ℝ)(i:Hot (Board R r)):ℝ:=
  gain G grades v i * probes (Join.left i.val) * (3:ℝ)^v

theorem occupied (K:Bulk.Kernel S p path O)(F:Forest S.ratio)(tag:S.Choices)
    (M:ι→Row P R G X)(w:V→ℝ)(grades:V→ℕ){σ cost:ℝ}{order count shelf:ℕ}
    (estate:Scene.Armada M w grades σ cost order count shelf)(hc:cost≤1)(hs:0<σ)(x:X)
    (layout:Layout G)(tape:Finset Age)(legal:Legal tape layout)(A:fieldDir G c 1)(hr:r≤order)
    (i:Hot (Board R r))(hit:(Join.left i.val).val.Nonempty)(z:Precision.Key F G→ℝ):
    let Y:=Air.craft M (fun a=>(M a).paint x) grades layout tape
    Poly.toll w (Join.left i.val)*‖Cloud.paint z (drivers K F tag Y A r i)‖ ≤
      salary G grades σ order shelf i*(1+‖(Bulk.translated K F A z).2‖)^(length grades i*(order+shelf+1)) := by
  let s:Hot R:=⟨Join.left i.val,hit⟩
  let t:=(Join.right i.val).val.card
  let k:=length grades i
  let v:=order+shelf+1
  let C:=2*(2*WilsonPositionProgramCurvedAngularPrice.price G k v+1)
  let b:=1+‖(Bulk.translated K F A z).2‖
  let α:=WilsonReceivedSourceCoefficientIncome.price G σ 1 order shelf
  have hα:0≤α:=by dsimp [α,WilsonReceivedSourceCoefficientIncome.price];positivity
  have old:=WilsonPositionProgramFiledOccupiedDriver.original K F tag M w grades estate hs x layout tape legal A hr i hit z
  rw [billed] at old
  have paid:=credit M w grades estate hc s.val
  apply old.trans
  change t.factorial*(C*(α*|(s.val.val.image P.origin).card*cost|))*b^(k*v)≤
    (t.factorial*|C| *(α*(Fintype.card V:ℝ)))*b^(k*v)
  apply mul_le_mul_of_nonneg_right _ (by dsimp [b];positivity)
  calc
    _ ≤ (t.factorial:ℝ)*(|C| *(α*(Fintype.card V:ℝ))) :=mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self C) (mul_le_mul_of_nonneg_left paid hα)
      (mul_nonneg hα (abs_nonneg _)) (abs_nonneg C)) (Nat.cast_nonneg _)
    _=_:=by ring

theorem released {G:Gauge}(n:Side)(e:ℕ)(p h:ℕ)(f:Side){a t C w b:ℝ}(ha:0≤a)(ht:0≤t)
    (hw:0≤w)(hb:0≤b)(x:ℝ)(sale:(n.val:ℝ)^e*x≤t*(C*(a*w*(2+‖(Stationary.arm G f 1).symm.toContinuousLinearMap‖)^h))*b^p):
    x≤((a/(n.val:ℝ)^e)*(t*|C| *w*(3:ℝ)^h))*b^p := by
  have hn:0<(n.val:ℝ)^e:=pow_pos (by exact_mod_cast n.property) _
  have hC:=le_abs_self C
  have axis:2+‖(Stationary.arm G f 1).symm.toContinuousLinearMap‖≤3:=by linarith [WilsonPositionProgramAngularArm.original G f 1]
  have tall:=pow_le_pow_left₀ (by positivity) axis h
  have priced:t*(C*(a*w*(2+‖(Stationary.arm G f 1).symm.toContinuousLinearMap‖)^h))*b^p≤
      t*(|C| *(a*w*(3:ℝ)^h))*b^p:=by gcongr
  have upper:=sale.trans priced
  calc
    x≤(t*(|C| *(a*w*3^h))*b^p)/(n.val:ℝ)^e := (le_div_iff₀ hn).2 (by rwa [mul_comm])
    _=_:=by field_simp

end YM.Integration.WilsonPositionProgramDatedDrivers
end
