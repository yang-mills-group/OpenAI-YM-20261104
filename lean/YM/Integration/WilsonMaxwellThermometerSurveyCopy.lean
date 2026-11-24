import YM.Integration.WilsonMaxwellThermometerSurveyRoster

/-! Realization of the same prepared W source as an authentic Rocket registry
and as a normalized W.tree integral at the original translated sites. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSurveyCopy
open Function Finset Lattice Wilson RG Labels Source XSpace RegulatorIR.FVAAlt2
open PhysicalNext.Repeat.Legato Precision PertExtension PertExtension.Orb
open WilsonThermometerPositionTunedSurvey (prepared represents sound)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)(W:Initialize G)

def registry : YM.FVAAlt2.Lobby.Registry R.family.labels R.family.params:=
  ⟨prepared R W,sound R W,fun d=>(represents R W d).2.1⟩

variable (p:XSpace.Period){I:Type} [Fintype I] [LinearOrder I](d:I→ℕ)(z:I→ Cover)
    (a:(j:I)→(R.family.labels.level (d j)).Index)

def planted:Config G p.side→ℝ:=Kick.topMark (registry R W) univ d a p.side z

theorem observed : PreTest (planted R W p d z a):=
  YM.FVAAlt2.Home.Profiles.frameKeys (registry R W) d a (wrap p.side ∘ z) ⟨p.large,p.even⟩

theorem original (D:ChartRatio G)(law:LocalRatio D)(T:p.Tree)(q:ℕ):
    PowerSeries.coeff q (WilsonThermometerPositionTunedCorrection.surveyed R W d p z T a)=
      (YM.FVAAlt2.Fixed.treeMom D (planted R W p d z a) (Kick.depthF univ d a) q:ℂ):=by
  let X:=planted R W p d z a
  have hX:=observed R W p d z a
  have one : PreTest ((1:ℝ) • X):=by simpa [X] using hX
  have charts:=YM.FVAAlt2.Home.Profiles.diag_sm D law X 1 (even_iff_two_dvd.mpr p.even) hX one
  have same : diag (restrictedO X) = diagonalWith D (restrictedO X):=by
    simpa only [one_smul,Orb.diag] using charts
  have field : Complex.ofRealCLM ∘ (X ∘ T.links)=∏j,WilsonThermometerPositionTunedChange.letter R W p T d z a j:=by
    funext u
    simp only [Function.comp_apply,X,planted,Kick.topMark,Finset.prod_apply]
    change (↑((∏j:I,SlotEvaluation.fieldAt (prepared R W (d j)) (a j) (wrap p.side (z j)) (T.links u)):ℝ):ℂ)=
      ∏j,WilsonThermometerPositionTunedChange.letter R W p T d z a j u
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun j _=>SlotEvaluation.scalar_real (sound R W (d j)))
  have paid:=congrArg (PowerSeries.coeff (q+Kick.depthF univ d a))
    (congrArg ((Bare.normalized T G) ·) (WilsonThermometerPositionTunedChange.shipped R W p T d z a))
  rw [← field,show (PowerSeries.X ^ Kick.depthF univ d a :Bare.Series T G)=
      Bare.scalar T (PowerSeries.X ^ Kick.depthF univ d a) by simp [Bare.scalar],Bare.normalized_scalar,
    PowerSeries.coeff_X_pow_mul] at paid
  change _=(_ : ℂ)
  rw [WilsonThermometerPositionTunedCorrection.surveyed,←paid,FVA2.XPos.genuine_X T hX,
    PowerSeries.coeff_map,PowerSeries.coeff_mk,same]
  rfl

end YM.Integration.WilsonMaxwellThermometerSurveyCopy
end
