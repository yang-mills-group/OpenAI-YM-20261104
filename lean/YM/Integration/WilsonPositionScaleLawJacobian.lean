import YM.Integration.WilsonPositionScaleLawBranch

/-! The after-branch Jacobian is calculated on one physical home and the true
calibrated transition is the unique near-identity zero of its finite equations.
The neighborhood and operator Lipschitz constant are fixed before targets. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawJacobian
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Normalize WilsonPositionScaleLawHome WilsonPositionScaleLawNative WilsonPositionScaleLawBranch
open WilsonPhysicalPositionBornCandidates (record faithful operator expansion)
open WilsonPhysicalPositionDiscreteBranches (field)
open scoped Topology Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(V:Store G)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field

abbrev fieldsAt (d:ℕ)(z:ℝ×Ratio):Prediction G d:=bank F J V d z.1 z.2.val
abbrev chart (d:ℕ)(z:ℝ×Ratio):MoveSpace G d:=coordinates F J V d z

theorem approaches (lead:Leading F J)(d:ℕ)(raw:Raw J d):Tendsto (chart F J V d) sweep (𝓝 0):=by
  let X:=E d
  let I:=ContinuousLinearMap.id ℂ X
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  let B:=record G C d
  obtain ⟨L,hL⟩:=LinearMap.exists_leftInverse_of_injective (K:=ℝ) B (LinearMap.ker_eq_bot.mpr (faithful C))
  have ha:Tendsto (fun z=>exactOp F J V d z-I) sweep (𝓝 0):=by
    have t:Tendsto (exactOp F J V d) sweep (𝓝 I):=transferred F J V lead d raw
    simpa only [sub_self] using t.sub_const I
  have hrecord:Tendsto (fun z=>B (chart F J V d z)) sweep (𝓝 0):=by
    apply ha.congr'
    filter_upwards [realizes F J V lead d] with z h
    rw [←h,expansion];abel
  have fin:= (L.continuous_of_finiteDimensional.tendsto (0:X→L[ℂ]X)).comp hrecord
  rw [map_zero] at fin
  exact fin.congr fun z=>DFunLike.congr_fun hL (chart F J V d z)

theorem calibrated (lead:Leading F J)(d:ℕ):∀ᶠr in trail,
    (V.measure d).D (WilsonPositionPrescribedScreen.hierarchy F (positioned F J V) d r)=(V.measure d).D (reference G d):=by
  filter_upwards [(WilsonPositionPrescribedScreen.original F J lead V d).2,RG17.positiveLength] with r fit hr
  have eq:WilsonPositionPrescribedScreen.hierarchy F (positioned F J V) d r=
      recruit (stand (WilsonPositionPrescribedScreen.correction F J V d r)) (WilsonPositionPrescribedScreen.hierarchy F J d r):=by
    funext n
    apply LinearMap.ext;intro φ;apply MultilinearMap.ext;intro v
    change WilsonPositionPrescribedScreen.hierarchy F (positioned F J V) d r n φ v=
      WilsonPositionPrescribedScreen.hierarchy F J d r n φ (fun j=>stand (WilsonPositionPrescribedScreen.correction F J V d r) (v j))
    rw [WilsonPositionPrescribedScreen.actual F (positioned F J V) _ _ _ _ hr,WilsonPositionPrescribedScreen.actual F J _ _ _ _ hr]
    apply congrArg φ.applyTo;funext x
    apply congrArg (S.classMoment (spectator F none) (fun _:Fin n=>d) (r•x));funext j
    exact congrArg (J r d) (WilsonPositionPrescribedFrame.leg F J V fit.2.1 (v j))
  rw [eq];exact fit.1

theorem recovered (lead:Leading F J)(d:ℕ)(raw:Raw J d):∀ᶠz in sweep,
    chart F J V d z=(V.survey d).route (V.prepared d) ((V.survey d).purse (fieldsAt F J V d z)):=by
  let D:=V.survey d
  let P:=fieldsAt F J V d
  let a:=chart F J V d
  have input:Tendsto (fun z=>(D.purse (P z),a z)) sweep (𝓝 D.opening):=
    (WilsonPositionScaleLawHome.original F J V lead d).prodMk_nhds (approaches F J V lead d raw)
  filter_upwards [exactEquation F J V lead d,bothHomes.eventually
    (calibrated F J V lead d),input.eventually (D.pathway (V.prepared d))] with z hfar hit localEq
  have same:Fray.SetEq (V.measure d) ((guide G d).symm (a z)) (P z):=by
    change (V.measure d).D (recruit (field (a z)) (P z))=_
    rw [hfar]
    exact hit
  have hg:=(D.means _ _).mp same
  rw [(guide G d).apply_symm_apply] at hg
  exact (localEq.mp hg).symm

def derivative (d:ℕ)(z:ℝ×Ratio):MoveSpace G d→L[ℝ]MoveSpace G d:=
  (V.survey d).delta ((V.survey d).purse (fieldsAt F J V d z),chart F J V d z)

theorem original (lead:Leading F J)(d:ℕ)(raw:Raw J d):
    Tendsto (derivative F J V d) sweep (𝓝 1) ∧
    (∀ᶠ z in sweep,(derivative F J V d z).IsInvertible) ∧
    Tendsto (fun z=>(derivative F J V d z).inverse) sweep (𝓝 1):=by
  let D:=V.survey d
  let H:=V.prepared d
  have input:Tendsto (fun z=>(D.purse (fieldsAt F J V d z),chart F J V d z)) sweep (𝓝 D.opening):=
    (WilsonPositionScaleLawHome.original F J V lead d).prodMk_nhds (approaches F J V lead d raw)
  have hj:= (D.continuous_steps.tendsto D.opening).comp input
  have inv:= ((D.pin_inv H).contDiffAt_map_inverse (n:=1)).continuousAt.tendsto.comp hj
  have at0:(D.delta D.opening).inverse=(1:MoveSpace G d→L[ℝ]MoveSpace G d):=by
    rw [D.unpin H];exact ContinuousLinearMap.inverse_equiv (.refl ℝ _)
  rw [at0] at inv
  rw [D.unpin H] at hj
  exact ⟨hj,input.eventually (D.unhit H),inv⟩

theorem quantitative (lead:Leading F J)(d:ℕ)(raw:Raw J d):∃L:ℝ,0≤L ∧
    ∃U∈𝓝 (V.survey d).opening.1,∀ᶠz in sweep,∀y∈U,
      ‖exactOp F J V d z-operator C ((V.survey d).route (V.prepared d) y)‖≤
        L*‖(V.survey d).purse (fieldsAt F J V d z)-y‖:=by
  let D:=V.survey d
  let X:=E d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  let B:MoveSpace G d→L[ℝ](X→L[ℂ]X):=(record G C d).toContinuousLinearMap
  have diff(a b:MoveSpace G d):operator C a-operator C b=B (a-b):=by
    rw [expansion,expansion,B.map_sub];change _=record G C d a-record G C d b;abel
  obtain ⟨A,U,hu,lip⟩:=((D.train (V.prepared d)).of_le (by decide : 1≤ω)).exists_lipschitzOnWith
  refine ⟨‖B‖*(A:ℝ),mul_nonneg (norm_nonneg _) A.coe_nonneg,U,hu,?_⟩
  filter_upwards [(WilsonPositionScaleLawHome.original F J V lead d).eventually hu,
    realizes F J V lead d,recovered F J V lead d raw] with z hz eq read y hy
  rw [←eq,diff]
  refine (B.le_opNorm _).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [show coordinates F J V d z=D.route (V.prepared d) (D.purse (fieldsAt F J V d z)) from read]
  exact (dist_eq_norm ..).symm.trans_le ((lip.dist_le_mul _ hz _ hy).trans_eq (by rw [dist_eq_norm]))

end YM.Integration.WilsonPositionScaleLawJacobian
end
