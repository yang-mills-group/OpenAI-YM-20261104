import YM.Integration.WilsonPositionProgramCurvedPrimitiveSalary
import YM.Integration.WilsonPositionProgramHeatedWallet

/-! The actual positive-radius salary for every occupied primitive of the lower Wilson Gaussian. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramFiledOccupiedDriver
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02 Next.Rank
open Comparison.RG02.Cumulants Comparison.RG02.Order Comparison.RG02.Assembly
open WilsonPositionProgramFiledGaussianChange WilsonPositionProgramHeatedWallet
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise AllOrder AllOrder.Floe AllOrder.Floe.Step
open scoped BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{path:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p path O)(F:Forest S.ratio)(tag:S.Choices)
  {V X ι:Type}[DecidableEq V][Fintype V]{R:Census V}{P:Passport f V}

theorem primitive (W:Bulk.Colors R G f)(A:fieldDir G c 1){r:ℕ}(i:Hot (Board R r))
    (hit:(Join.left i.val).val.Nonempty)(z:Precision.Key F G→ℝ):
    let d:=(Join.right i.val).val.card
    let s:Hot R:=⟨Join.left i.val,hit⟩
    let b:=(Bulk.translated K F A z).2
    Cloud.paint z (drivers K F tag W A r i)=(d.factorial:ℂ)*Assembly.jet (Bulk.markFn S F W s) (W.power s+d) (1,b):=by
  dsimp only
  have t:Assembly.translate (Bulk.stage K F A) (Bulk.hinge F) z=(1,(Bulk.translated K F A z).2):=by
    change Bulk.translated K F A z=_
    rw [Bulk.footing]
  simp only [drivers,Assembly.generator,dif_pos hit,map_smul,Assembly.reading,t,smul_eq_mul]

theorem original (M:ι→Row P R G X)(w:V→ℝ)(grades:V→ℕ){σ cost:ℝ}{order count shelf:ℕ}
    (estate:Scene.Armada M w grades σ cost order count shelf)(hs:0<σ)(x:X)(layout:Layout G)
    (tape:Finset Age)(legal:Legal tape layout)(A:fieldDir G c 1){r:ℕ}(hr:r≤order)
    (i:Hot (Board R r))(hit:(Join.left i.val).val.Nonempty)(z:Precision.Key F G→ℝ):
    let Y:=Air.craft M (fun a=>(M a).paint x) grades layout tape
    let t:=(Join.right i.val).val.card
    let s:Hot R:=⟨Join.left i.val,hit⟩
    let h:=Y.power s+t
    let v:=order+shelf+1
    let b:=(Bulk.translated K F A z).2
    let price:=WilsonReceivedSourceCoefficientIncome.price G σ 1 order shelf*|(s.val.val.image P.origin).card*cost|
    Poly.toll (deployed w r) i.val*‖Cloud.paint z (drivers K F tag Y A r i)‖ ≤
      (t.factorial:ℝ)*(2*(2*WilsonPositionProgramCurvedAngularPrice.price G h v+1)*price)*(1+‖b‖)^(h*v):=by
  let Y:=Air.craft M (fun a=>(M a).paint x) grades layout tape
  let t:=(Join.right i.val).val.card
  let s:Hot R:=⟨Join.left i.val,hit⟩
  let v:=order+shelf+1
  let b:=(Bulk.translated K F A z).2
  have ht:t≤order:=le_trans (by simpa only [Fintype.card_fin] using card_le_univ (Join.right i.val).val) hr
  have held:=WilsonPositionProgramCurvedPrimitiveSalary.original F M w grades estate hs x layout tape legal s t ht b
  dsimp only
  rw [billed,primitive K F tag Y A i hit z,norm_mul,Complex.norm_natCast]
  exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left held (Nat.cast_nonneg t.factorial)).trans_eq (by ring))

end YM.Integration.WilsonPositionProgramFiledOccupiedDriver
end
