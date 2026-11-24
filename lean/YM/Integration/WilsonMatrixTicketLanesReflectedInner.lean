import YM.Integration.WilsonMatrixTicketLanesReflectedJets
import YM.Integration.WilsonMatrixTicketLanesReflectedQuadratic

/-! The angular word price on the finite original Wilson torus has the actual FVA2 inner covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReflectedInner
open Function Filter MeasureTheory Finset Lattice RG Tree Gauge Wilson Precision PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Stack
open FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.OpenSlots RGComparison.Core16 RGComparison.Core16.Lumen
open RGComparison.Core16.Lumen.Planet RGComparison.Core16.Silk FVA2 FVA2.CityHistory FVA2.RayScatter
open WilsonMatrixTicketLanesReflectedJets
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f) (T : Forest S.ratio)
    {P : Parcel.Oven S.patch} (X : P.Form G) (offer : P.Offers X S.kernel) (large : Bid.Larger (G:=G) S)
    (tag : S.Choices) (nil : (Descent.nil (top:=f)).Tags)
local notation "O" => Spool.lens (S:=S) (0:Directions G c) X T
local notation "linkChart" => Next.Foundations.chart G

def precision : Quadratic (Future G S T × Pins G c) := gateQ S T tag (retained Descent.nil nil trivial)

include large in
theorem sound : (precision (G:=G) S T tag nil).core.RespectsPrice :=
  useful S T Descent.nil nil tag large trivial

def law : Law (Future G S T) := (sound S T large tag nil).inner

def axis (e : Wire G T.Free) : Module.Dual ℝ (Future G S T) :=
  (EuclideanSpace.proj e.2).toLinearMap ∘ₗ LinearMap.proj e.1

omit large tag nil in
private theorem entered (w : Rail G T.Free) (v : Fk.Door G T.Free) :
    weft w (Fk.scene (swatch w) v)=deposited (K:=Pins G c) w (RayScatter.recover (0:Pins G c) v) := by
  let a (e : Wire G T.Free) := turn (v.2 e.1) e.2
  change (∏i : Fin w.length,a w[i]) = (w.map a).prod
  have ht : w.map a = List.ofFn (fun i : Fin w.length => a w[i]) := by
    have ordered : List.ofFn (fun i : Fin w.length=>w[i])=w := List.ofFn_getElem
    simpa only [List.map_ofFn,Function.comp_def] using congrArg (List.map a) ordered.symm
  rw [ht,List.prod_ofFn]

include offer large

theorem filed (w : Rail G T.Free) : Silk.price O w = Stack.drop w.length (Stack.read (0:Pins G c)
    (solenoid S T Descent.nil nil tag linkChart 1 large trivial (Stack.rise (deposited (K:=Pins G c) w)))) := by
  have pin : ∀ i, ‖(0 : Directions G c) i‖≤X.Q := by simp [offer.good.thick.1.le]
  have row:=Fork.perch O linkChart (Next.Foundations.chart_ok G) (Spot.thermalHeat S T tag large)
    (precision S T tag nil) (Spot.precisionHeat S T tag large nil) (sound S T large tag nil) (0:Pins G c)
    (ψ:=weft w) (swatch w) (Spot.prospect S T tag 0 large P X offer pin) (deposited (K:=Pins G c) w)
    (Eventually.of_forall (entered S T w)) (hot w) w.length
  simpa only [Silk.price,solenoid,Pi.one_apply,Spot.fusionL S T linkChart tag large nil,precision,sound] using row

/-- Every free angular word is read by the actual inner Gaussian, without a gauge-invariance premise on its letters. -/
theorem moment (w : Rail G T.Free) : nth 0 (Silk.price O w) =
    (law S T large tag nil).average (tangent G T.Free) (fun x=>(w.map fun e=>x e.1 e.2).prod) := by
  rw [filed S T X offer large tag nil,Silk.nth,Stack.drop,coeff_mk,Nat.add_zero,solenoid,expansion]
  have paid:=CityHistory.primeZ (S:=S) (T:=T) (d:=Descent.nil) (t:=nil) (b:=tag) (Z:=linkChart)
    (z:=1) (hz:=Next.Foundations.chart_ok G) (h:=large) (H:=trivial)
  rw [WilsonMatrixTicketLanesReflectedQuadratic.initial _ _ _ _ paid]
  simp only [base]; rfl

/-- The zero coefficient of the signed connected two-link price is precisely this entry of the
retained lower conditional Hessian inverse (two original means evaluated separately). -/
theorem covariance (i j : Wire G T.Free) : nth 0 (Silk.gap O [i] [j]) =
    (law S T large tag nil).wick (axis S T i) (axis S T j) := by
  let Γ:=law S T large tag nil
  let μ:=tangent G T.Free
  have zero (v : Wire G T.Free) : nth 0 (Silk.price O [v])=0 := by
    rw [moment S T X offer large tag nil]
    have ex:=Γ.recursion μ (axis S T v) (fun _:Unit=>axis S T v) (∅:Finset Unit)
    simpa [Law.product,Γ,μ,axis] using ex
  have pair:=Γ.recursion μ (axis S T i) (fun _:Unit=>axis S T j) ({()}:Finset Unit)
  change PowerSeries.coeff 0 (Silk.price O [j,i]-Silk.price O [j]*Silk.price O [i])=_
  simp only [coeff_zero_eq_constantCoeff_apply,map_sub,map_mul]
  simp only [←coeff_zero_eq_constantCoeff_apply]
  change nth 0 (Silk.price O [j,i])-nth 0 (Silk.price O [j])*nth 0 (Silk.price O [i])=_
  rw [zero,zero,mul_zero,sub_zero,moment S T X offer large tag nil]
  simp only [Finset.sum_singleton,Finset.erase_singleton] at pair
  rw [show Law.product (fun _ : Unit=>axis S T j) ∅=1 from funext (fun _=>Finset.prod_empty),Γ.empty μ] at pair
  simpa [Law.product,Γ,μ,axis] using pair

end YM.Integration.WilsonMatrixTicketLanesReflectedInner
