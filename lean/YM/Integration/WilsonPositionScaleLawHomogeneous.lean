import YM.Integration.WilsonPositionScaleLawTrajectory
import YM.Integration.WilsonPositionHomogeneousFrame

/-! The purchased genuine mass-independent adjustment has exact unit diagonal.
Thus it preserves the highest component of a fixed infrared field at every
physical radius, including the inverse coordinate used in qgr. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawHomogeneous
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (positioned sweep)
open WilsonPositionScaleLawGrade (grade reads)
open WilsonPositionScaleLawFixed (top normalized)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawQinter (measured)
open WilsonPositionHomogeneousCoefficients (Warrant)
open WilsonPositionHomogeneousFrame (homogeneous turn change)
open private peak from YM.Integration.WilsonPositionScaleLawFixed
open private leg from YM.Integration.WilsonPositionHomogeneousFrame
open scoped Topology Classical Asymptotics
variable {G:Gauge}(Z:WilsonPrescription G){R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

theorem action (H:Warrant Z)(d:ℕ)(r:ℝ)(v:E d):grade R.family (top d) (change F J Z d r v)=grade R.family (top d) v:=by
  let T:=turn F J Z d r
  let A:=stand T
  by_cases fit:Bijective A
  · have band:Level.Band A:=fun l hl p hp=>Submodule.add_mem _ hp (T.property.2.1 l hl p hp)
    have diag:Level.diag A=1:=WilsonPositionHomogeneousNear.diagonal Z H d (kinetic Z F J r)
    obtain ⟨x,rfl⟩:=(fields R.family.labels d).symm.surjective v
    apply (fields R.family.labels d).injective
    rw [reads,reads,leg F J Z fit,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    calc
      _=Level.proj (top d) (A (Level.proj (top d) x)):=peak band x
      _=Level.diag A (Level.proj (top d) x):=(Level.diagonals x (top d) A).symm
      _=_:=by rw [diag];rfl
  · rw [change,dif_neg fit];rfl

theorem invariant (H:Warrant Z)(d:ℕ)(r:ℝ)(O:S.Field d):
    grade R.family (top d) ((homogeneous F J Z r d).symm O)=
      grade R.family (top d) ((positioned F J Z.store r d).symm O):=by
  let P:=grade R.family (top d)
  let B:=change F J Z d r
  let x:=(positioned F J Z.store r d).symm O
  change P (B.symm x)=P x
  calc
    _=P (B (B.symm x)):=(action Z F J H d r _).symm
    _=P x:=congrArg P (B.apply_symm_apply x)


def column (d:ℕ)(r:ℝ)(O:S.Field d):E d:=(r:ℂ)^d • grade R.family (top d) ((homogeneous F J Z r d).symm O)

theorem identifies (H:Warrant Z)(d:ℕ)(r:ℝ)(n:ℕ)(O:S.Field d):
    column Z F J d (radius r n) O=normalized F J Z d r n O:=congrArg ((radius r n:ℂ)^d • ·) (invariant Z F J H d _ O)

variable {hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (d:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d)
    (observed:(measured Z M ν F J d 2)=o[sweep] (fun z=>kinetic Z F J z.1^2))
    (funded:Coupling G (kinetic Z F J))(r:ℝ)(hr:0<r)

include H lead paid raw observed funded hr in
theorem original:∃N p:ℕ,∀k:ℕ,∀O:S.Field d,
    let ratio:=(((N+k:ℕ):ℝ)+1)^p/((N:ℝ)+1)^p
    ‖column Z F J d (radius r (N+k)) O‖≤ratio*‖column Z F J d (radius r N) O‖ ∧
    ‖column Z F J d (radius r N) O‖≤ratio*‖column Z F J d (radius r (N+k)) O‖:=by
  obtain ⟨N,p,all⟩:=WilsonPositionScaleLawTrajectory.original Z M H ν F J lead paid d raw observed funded r hr
  refine ⟨N,p,?_⟩
  intro k O
  simp only [identifies Z F J (WilsonPositionHomogeneousCoefficients.purchased Z H)]
  exact all k O

end YM.Integration.WilsonPositionScaleLawHomogeneous
end
