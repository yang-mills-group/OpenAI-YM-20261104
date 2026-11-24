import YM.Integration.WilsonMatrixTicketLanesReflectedInner
import YM.Integration.WilsonMatrixTicketLanesRetainedPrincipal

/-! The angular word price on the finite original Wilson torus has the actual FVA2 inner covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedAngular
open Function Filter MeasureTheory Finset Lattice RG Tree Gauge Wilson Precision PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Stack
open FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.OpenSlots RGComparison.Core16 RGComparison.Core16.Lumen
open RGComparison.Core16.Lumen.Planet RGComparison.Core16.Silk FVA2 FVA2.CityHistory FVA2.RayScatter
open WilsonMatrixTicketLanesReflectedJets
open scoped Topology ContDiff Classical BigOperators
open WilsonMatrixTicketLanesReflectedInner FormalOPE.RG10.MultiGauge.Papers
variable {G : Gauge} {c f : Side} (S : StepData c f) (T : Forest S.ratio)
    {P : Parcel.Oven S.patch} (X : P.Form G) (offer : P.Offers X S.kernel) (large : Bid.Larger (G:=G) S)
    (tag : S.Choices) (nil : (Descent.nil (top:=f)).Tags)
variable (u : Directions G c) (pin : ∀ i,‖u i‖≤X.Q)
local notation "O" => Spool.lens (S:=S) u X T
local notation "linkChart" => Next.Foundations.chart G

def changeField := (precision (G:=G) S T tag nil).skew (sound S T large tag nil) u

private theorem entered (w : Rail G T.Free) (v : Fk.Door G T.Free) :
    weft w (Fk.scene (swatch w) v)=deposited (K:=Pins G c) w (RayScatter.recover u v) := by
  let a (e : Wire G T.Free) := turn (v.2 e.1) e.2
  change (∏i : Fin w.length,a w[i]) = (w.map a).prod
  have ht : w.map a = List.ofFn (fun i : Fin w.length => a w[i]) := by
    have ordered : List.ofFn (fun i : Fin w.length=>w[i])=w := List.ofFn_getElem
    simpa only [List.map_ofFn,Function.comp_def] using congrArg (List.map a) ordered.symm
  rw [ht,List.prod_ofFn]

def coordinate (i : Wire G T.Free) : Permit (Future G S T) := ⟨axis S T i,Papers.linear (axis S T i)⟩

include offer large pin

theorem filed (w : Rail G T.Free) : Silk.price O w = Stack.drop w.length (Stack.read u
    (solenoid S T Descent.nil nil tag linkChart 1 large trivial (Stack.rise (deposited (K:=Pins G c) w)))) := by
  have row:=Fork.perch O linkChart (Next.Foundations.chart_ok G) (Spot.thermalHeat S T tag large)
    (precision S T tag nil) (Spot.precisionHeat S T tag large nil) (sound S T large tag nil) u
    (ψ:=weft w) (swatch w) (Spot.prospect S T tag u large P X offer pin) (deposited (K:=Pins G c) w)
    (Eventually.of_forall (entered S T u w)) (hot w) w.length
  simpa only [Silk.price,solenoid,Pi.one_apply,Spot.fusionL S T linkChart tag large nil,precision,sound] using row

/-- Every free angular word is read by the actual inner Gaussian, without a gauge-invariance premise on its letters. -/
theorem moment (w : Rail G T.Free) : nth 0 (Silk.price O w) =
    (law S T large tag nil).average (tangent G T.Free) (fun x=>(w.map fun e=>(x+changeField S T large tag nil u) e.1 e.2).prod) := by
  rw [filed S T X offer large tag nil u pin,Silk.nth,Stack.drop,coeff_mk,Nat.add_zero,solenoid,expansion]
  have paid:=CityHistory.primeZ (S:=S) (T:=T) (d:=Descent.nil) (t:=nil) (b:=tag) (Z:=linkChart)
    (z:=1) (hz:=Next.Foundations.chart_ok G) (h:=large) (H:=trivial)
  rw [WilsonMatrixTicketLanesRetainedPrincipal.initial _ _ _ _ _ paid]
  simp only [base]; rfl



/-- The genuine angular price at nonzero retained field. Each separately deposited original mean is present. -/
theorem connected (i j : Wire G T.Free) : nth 0 (Silk.gap O [i] [j]) =
    (law S T large tag nil).wick (axis S T i) (axis S T j) := by
  let Γ:=law S T large tag nil
  let μ:=tangent G T.Free
  let a:=changeField S T large tag nil u
  let B:=opening μ Γ
  let I:=coordinate S T i
  let J:=coordinate S T j
  rw [←WilsonMatrixTicketLanesReflectedInner.covariance S T X offer large tag nil i j]
  change coeff 0 (_-_*_) = coeff 0 (_-_*_)
  simp only [coeff_zero_eq_constantCoeff_apply,map_sub,map_mul]
  simp only [←coeff_zero_eq_constantCoeff_apply]
  change nth 0 (Silk.price O [j,i])-nth 0 (Silk.price O [j])*nth 0 (Silk.price O [i]) =
    nth 0 (Silk.price (Spool.lens (S:=S) 0 X T) [j,i])-nth 0 (Silk.price (Spool.lens (S:=S) 0 X T) [j])*nth 0 (Silk.price (Spool.lens (S:=S) 0 X T) [i])
  rw [moment S T X offer large tag nil u pin,moment S T X offer large tag nil u pin,moment S T X offer large tag nil u pin]
  rw [WilsonMatrixTicketLanesReflectedInner.moment S T X offer large tag nil,WilsonMatrixTicketLanesReflectedInner.moment S T X offer large tag nil,WilsonMatrixTicketLanesReflectedInner.moment S T X offer large tag nil]
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  have charged:= WilsonMatrixTicketLanesRetainedPrincipal.covariance_translate B (starts μ Γ) J I (axis S T j a) (axis S T i a)
  change Γ.average μ (fun x=>(x j.1 j.2+a j.1 j.2*1)*(x i.1 i.2+a i.1 i.2*1))-
    Γ.average μ (fun x=>x j.1 j.2+a j.1 j.2*1)*Γ.average μ (fun x=>x i.1 i.2+a i.1 i.2*1)=
    Γ.average μ (fun x=>x j.1 j.2*x i.1 i.2)-Γ.average μ (fun x=>x j.1 j.2)*Γ.average μ (fun x=>x i.1 i.2) at charged
  simpa only [Pi.add_apply,PiLp.add_apply,mul_one] using charged

end YM.Integration.WilsonMatrixTicketLanesRetainedAngular
