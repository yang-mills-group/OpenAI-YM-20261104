import YM.Integration.WilsonPositionProgramFiledPrimitiveSalary

/-! All occupied driver jets of the actual filed Wilson row at its own receiving source radius. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramCurvedPrimitiveSalary
open Filter Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Exterior Stationary Comparison.RG02 Comparison.RG02.Assembly AllOrder AllOrder.Floe AllOrder.Floe.Step
open Comparison.RG02.Valence Comparison.RG02.Adjacent FVA1Physical.Wilson Precision
open WilsonPositionProgramThermalPolar WilsonReceivedSourceCoefficientIncome
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius Topology
variable {V X ι:Type}[DecidableEq V]{G:Gauge}{c f:Side}{S:StepData c f}{P:Passport f V}{R:Census V}

theorem deposited (F:Tree.Forest S.ratio)(W:Bulk.Colors R G f)(s:Multi.Hot R)(k:ℕ)(b:Bulk.SliceDir S F G):
    jet (Bulk.markFn S F W s) k (1,b)=
    jet ((Bulk.projected (W.mark s)) ∘ WilsonPositionProgramAngularChart.chart (Work.F03.axisLog F)) k (1,b):=by
  have equal:Bulk.markFn S F W s=ᶠ[𝓝 0]
      (Bulk.projected (W.mark s)) ∘ WilsonPositionProgramAngularChart.chart (Work.F03.axisLog F):=by
    have prior:=continuous_snd.tendsto (0:Bulk.Joint S F (G:=G))
    filter_upwards [prior.eventually (Work.F03.inclusion_works F)] with x hx
    change W.mark s x.1 (Work.F03.live F x.2)=W.mark s x.1 (represent (Work.F03.axisLog F x.2))
    rw [hx]
  unfold jet
  rw [(equal.iteratedFDeriv ℝ k).eq_of_nhds]

theorem original (F:Tree.Forest S.ratio)(M:ι→Row P R G X)(w:V→ℝ)(grades:V→ℕ)
    {σ cost:ℝ}{order count shelf:ℕ}(estate:Scene.Armada M w grades σ cost order count shelf)
    (hs:0<σ)(x:X)(layout:Layout G)(tape:Finset Age)(legal:Legal tape layout)
    (s:Multi.Hot R)(t:ℕ)(ht:t≤order)(b:Bulk.SliceDir S F G):
    let Y:=Air.craft M (fun v=>(M v).paint x) grades layout tape
    let J:=Y.power s+t
    let v:=order+shelf+1
    let B:=price G σ 1 order shelf*|(s.val.val.image P.origin).card*cost|
    Poly.toll w s.val*‖jet (Bulk.markFn S F Y s) J (1,b)‖ ≤
      2*(2*WilsonPositionProgramCurvedAngularPrice.price G J v+1)*B*(1+‖b‖)^(J*v) := by
  let Y:=Air.craft M (fun a=>(M a).paint x) grades layout tape
  let J:=Y.power s+t
  let v:=order+shelf+1
  let B:=price G σ 1 order shelf*|(s.val.val.image P.origin).card*cost|
  let weight:=Poly.toll w s.val
  have b0:0≤B:=by dsimp [B,price];positivity
  have w0:0<weight:=Poly.worth estate.positive s.val
  have staff:=Air.license M (fun a=>(M a).paint x) grades w estate hs (fun a=>estate.honor a x)
  have mark:=((Air.standard M _ grades staff layout tape legal).1).suppose_mark s
  have annual:∀d≤J,∀u:fieldDir G f 1,
      ‖jet (Bulk.projected (Y.mark s)) d (1,u)‖≤ (B/weight)*(1+‖u‖)^v:=by
    intro d hd u
    by_cases under:d<Y.power s
    · rw [mark.jet_z _ under,norm_zero];positivity
    have booked:d-Y.power s≤order:=by dsimp [J] at hd;omega
    have sale:=WilsonPositionProgramFiledPrimitiveSalary.filed M w grades estate hs x layout tape s.val
      (d-Y.power s) booked u
    change weight*‖(Air.discharge Y (d-Y.power s) u).part s.val‖≤B*(1+‖u‖)^v at sale
    rw [Air.discharge,Multi.part_lit _ s] at sale
    have faced:Y.power s+(d-Y.power s)=d:=by omega
    change weight*‖jet (Bulk.projected (Y.mark s)) (Y.power s+(d-Y.power s)) (1,u)‖≤B*(1+‖u‖)^v at sale
    rw [faced] at sale
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ w0).2
    rwa [mul_comm]
  let C:=2*(2*WilsonPositionProgramCurvedAngularPrice.price G J v+1)
  have moved:=WilsonPositionProgramCurvedOccupiedPrice.original F (Bulk.projected (Y.mark s)) mark.smooth J v
    (B/weight) (div_nonneg b0 w0.le) annual b
  change weight*‖jet (Bulk.markFn S F Y s) J (1,b)‖ ≤ C*B*(1+‖b‖)^(J*v)
  rw [deposited]
  calc
    _ ≤ weight*(C*((B/weight)*(1+‖b‖)^(J*v))) := mul_le_mul_of_nonneg_left moved w0.le
    _ = _:=by field_simp

end YM.Integration.WilsonPositionProgramCurvedPrimitiveSalary
end
