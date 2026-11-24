import YM.Integration.WilsonPositionScaleLawMeasuredMoves
import YM.Integration.WilsonMSDictionaryFarRead
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredOutput
open Filter Function Set Finset Maxwell Maxwell.Free XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale FVA2.Dframe FVA2.Position.OpenAxis
open MS MS.Land MS.Fleet MS.Theater MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}

abbrev Space (G:Gauge)(h:ℕ) := Toon G h→ℂ
def arms (h:ℕ) : Sec G h ≃ₗ[ℝ] Space G h :=
  (Daylight (Press.portDeck G) h).equivFun.restrictScalars ℝ
def recorded {h:ℕ}(T:FieldEnd G h) : Space G h→L[ℝ]Space G h :=
  ((arms h).toLinearMap ∘ₗ T.restrictScalars ℝ ∘ₗ (arms h).symm.toLinearMap).toContinuousLinearMap
def shift (h:ℕ) : MoveSpace G h→ₗ[ℝ](Space G h→L[ℝ]Space G h) where
  toFun x:=recorded (((guide G h).symm x).val)
  map_add' a b:=by
    apply ContinuousLinearMap.ext
    intro v
    change arms h (((guide G h).symm (a+b)).val ((arms h).symm v))=_
    rw [map_add]
    exact (arms h).map_add _ _
  map_smul' c a:=by
    apply ContinuousLinearMap.ext
    intro v
    change arms h (((guide G h).symm (c•a)).val ((arms h).symm v))=_
    rw [map_smul]
    exact (arms h).map_smul c _
def field (h:ℕ)(x:MoveSpace G h) : Space G h→L[ℝ]Space G h := 1+shift h x

theorem input {h:ℕ}(x:MoveSpace G h)(v:Sec G h) :
    field h x (arms h v)=arms h (Fray.box x v) := by
  change arms h v+arms h (((guide G h).symm x).val ((arms h).symm (arms h v)))=_
  rw [LinearEquiv.symm_apply_apply,Fray.box,stood,map_add]
theorem identity (h:ℕ) : field (G:=G) h 0=1 := by simp [field]
theorem smooth (h:ℕ) : ContDiff ℝ ω (field (G:=G) h) := contDiff_const.add (shift h).toContinuousLinearMap.contDiff
theorem invertible (h:ℕ) : ∀ᶠx in 𝓝 (0:MoveSpace G h),(field h x).IsInvertible := by
  have c:Tendsto (field (G:=G) h) (𝓝 0) (𝓝 1):=(identity h) ▸ (smooth h).continuous.continuousAt.tendsto
  filter_upwards [c.eventually (Units.isOpen.mem_nhds (show IsUnit (1:Space G h→L[ℝ]Space G h) from isUnit_one))] with x unit
  have b:=ContinuousLinearMap.isUnit_iff_bijective.mp unit
  exact ⟨ContinuousLinearEquiv.ofBijective (field h x) (LinearMap.ker_eq_bot.mpr b.1) (LinearMap.range_eq_top.mpr b.2),rfl⟩
theorem output {h:ℕ}(x:MoveSpace G h)(live:(field h x).IsInvertible)(v:Sec G h) :
    field h x ((field h x).inverse (arms h v))=arms h v := by
  obtain ⟨A,hA⟩:=live
  rw [←hA,ContinuousLinearMap.inverse_equiv]
  exact A.apply_symm_apply _
theorem undo {h:ℕ}(x:MoveSpace G h)(live:(field h x).IsInvertible)(v:Sec G h) :
    (field h x).inverse (arms h (Fray.box x v))=arms h v := by
  rw [←input]
  obtain ⟨A,hA⟩:=live
  rw [←hA,ContinuousLinearMap.inverse_equiv]
  exact A.symm_apply_apply _
theorem analytic {h:ℕ}(x:MoveSpace G h)(live:(field h x).IsInvertible) :
    ContDiffAt ℝ ω (fun y:MoveSpace G h=>(field h y).inverse) x :=
  (live.contDiffAt_map_inverse (n:=ω)).comp x (smooth h).contDiffAt

end YM.Integration.WilsonPositionScaleLawMeasuredOutput
