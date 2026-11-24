import YM.Integration.WilsonPositionScaleLawThermometerError
import YM.Integration.WilsonPositionScaleLawThermometerSmeared
import YM.Integration.WilsonPositionScaleLawThermometerStock
import YM.Integration.WilsonPositionScaleLawThermometerProfile

/-! The uniform numerical price for one original signed thermometer observation,
calculated from its seven ordinary trades and the known printed polynomial tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerBill
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio)
open WilsonPositionThermometerConnected (value)
open WilsonPositionScaleLawThermometerProfile (row)
open WilsonPositionScaleLawThermometerPrint (mass)
open scoped Topology BigOperators Classical Polynomial
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)[W:RangeSpec]

omit W in
private theorem offered (q:ℕ)(a:PowerSeries ℂ){C:ℝ}(hC:0≤C)(bound:∀k≤q,‖coeff k a‖≤C){u:ℂ}(hu:‖u‖≤1):
    ‖(trunc (q+1) a).eval u‖≤((q+1:ℕ):ℝ)*C:=by
  rw [WilsonPositionScaleLawThermometerSmeared.paper]
  calc _≤∑k∈range (q+1),‖coeff k a*u^k‖:=norm_sum_le _ _
       _≤∑_∈range (q+1),C:=by
         apply Finset.sum_le_sum;intro k hk;rw [norm_mul,norm_pow]
         exact (mul_le_mul (bound k (by have e:=Finset.mem_range.mp hk;omega)) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) hC).trans_eq (mul_one _)
       _=((q+1:ℕ):ℝ)*C:=by simp [nsmul_eq_mul]

include H in
theorem shelves (q:ℕ):∃B T:ℝ,0≤B ∧ 0≤T ∧ ∀t:Ratio,∀x∈tsupport (Rose.test Z.criterion),
    (∀v:Badge,∀u:ℂ,‖u‖≤1→‖(trunc (q+1) (row Z M ν t x v)).eval u‖≤B) ∧ mass q (row Z M ν t x)≤T:=by
  let X:=Ratio×tsupport (Rose.test Z.criterion)
  let a(z:X):=row Z M ν z.1 z.2.val
  obtain ⟨C,hC,bnd⟩:=WilsonPositionScaleLawThermometerProfile.bound Z M H ν q
  have f(z:X)(v:Badge)(k:ℕ)(hk:k≤q):‖coeff k (a z v)‖≤C:=bnd _ _ z.2.property _ _ hk
  obtain ⟨T,hT,cost⟩:=WilsonPositionScaleLawThermometerStock.original q a hC f
  refine ⟨((q+1:ℕ):ℝ)*C,T,by positivity,hT,fun t x hx=>⟨fun v u hu=>offered _ _ hC (bnd _ _ hx v) hu,cost (t,⟨x,hx⟩)⟩⟩

include H in
theorem original (q:ℕ):∃L T:ℝ,0≤L ∧ 0≤T ∧ ∀t:Ratio,∀x∈tsupport (Rose.test Z.criterion),∀u:ℂ,‖u‖≤1→
    ∀A:Badge→ℂ,∀e:ℝ,0≤e→e≤1→(∀v:Badge,v.Nonempty→‖A v-(trunc (q+1) (row Z M ν t x v)).eval u‖≤e)→
    ‖value A-(trunc (q+1) (b3 (row Z M ν t x))).eval u‖≤L*e+‖u‖^(q+1)*T:=by
  obtain ⟨B,T,hB,hT,h⟩:=shelves Z M H ν q
  let R:=B+1
  have hR:0≤R:=by dsimp [R];positivity
  refine ⟨1+6*R+6*R^2,T,by positivity,hT,?_⟩
  intro t x hx u hu A e he h1 income
  let p:=row Z M ν t x
  let b(v:Badge):=(trunc (q+1) (p v)).eval u
  have bp(v:Badge):‖b v‖≤B:=(h t x hx).1 _ _ hu
  have aR(v:Badge)(hv:v.Nonempty):‖A v‖≤R:=by
    calc _=‖(A v-b v)+b v‖:=by rw [sub_add_cancel]
         _≤‖A v-b v‖+‖b v‖:=norm_add_le ..
         _≤R:=by dsimp [R];linarith [income v hv,bp v]
  have hprice:=WilsonPositionScaleLawThermometerError.price A b hR he aR (fun v _=>(bp v).trans (by dsimp [R];linarith)) income
  have printed:=WilsonPositionScaleLawThermometerPrint.cost q p hu
  calc _≤‖value A-value b‖+‖value b-(trunc (q+1) (b3 p)).eval u‖:=by simpa only [dist_eq_norm] using dist_triangle (value A) (value b) ((trunc (q+1) (b3 p)).eval u)
       _≤(1+6*R+6*R^2)*e+‖u‖^(q+1)*T:=add_le_add hprice (printed.trans (mul_le_mul_of_nonneg_left (h t x hx).2 (by positivity)))

end YM.Integration.WilsonPositionScaleLawThermometerBill
end
