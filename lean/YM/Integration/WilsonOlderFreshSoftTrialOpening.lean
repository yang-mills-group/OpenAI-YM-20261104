import YM.Integration.WilsonOlderFreshSoftFigures
import YM.Integration.WilsonOriginalPublicTrialNormalization

/-! The actual Taylor-normalized group word at the station in its unsuspended physical basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftTrialOpening
open Function Finset Lattice Laurent Wilson RG Source Labels Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank WilsonCoeffUV.Mer.Rolls
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open XSpace PertExtension PertExtension.Orb RegulatorIR.FVAAlt2 WilsonOriginalPublicTrialFigure
open IndependentSourcePathFamily OriginalMarkedSourceComet
open private atom from YM.Integration.IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](D d:I→ℕ)
local notation "F" j:max => R.family.labels.level (d j)

def group (b:∀i,(F i).Index)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
    (z:I→ Cover)(n:Side)(U:Config G n):ℝ:=
  ∏i,∑m,(atom (WilsonOlderFreshSoftFigures.seed R D d b κ pt i m)).unmasked U (wrap n (z i))

theorem heard (b:∀i,(F i).Index)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(z:I→ Cover)(n:Side)(U:Config G n):
    group R D d b κ pt z n U=(Sound.Figure.prop R (fun _:Unit=>z) d b ()).Vt n U:=by
  have h:=congrFun (Boot.combined R univ d b z n) U
  have source:(∏i,(R.family.localSection (d i)).places (Pi.single (b i) 1) (wrap n (z i)) U)=
      (((Sound.Figure.prop R (fun _:Unit=>z) d b ()).Vt n U):ℂ):=by
    simpa [Finset.prod_apply,Function.comp_apply,Sound.Figure.prop,Boot.scout] using h.symm
  apply Complex.ofReal_injective
  rw [←source,group,Complex.ofReal_prod]
  apply prod_congr rfl
  intro i _
  rw [←WilsonOlderFreshSoftFigures.field R D d]
  apply Complex.conj_eq_iff_re.mp
  change star ((R.family.localSection (d i)).evaluate (Pi.single (b i) 1) _)=_
  let v:=(Pi.single (b i) 1:(F i).Coeff)
  have hreal:=(R.makes.sections (d i)).ordinary_real v (expandAt (wrap n (z i)) U)
  change (R.family.localSection (d i)).evaluate (star v) _=star ((R.family.localSection (d i)).evaluate v _) at hreal
  change star ((R.family.localSection (d i)).evaluate v _)=_
  rw [←hreal]
  have bar:star (Pi.single (b i) 1:(F i).Coeff)=Pi.single (b i) 1:=by funext k;simp [Pi.single_apply]
  change (R.family.localSection (d i)).evaluate (star (Pi.single (b i) 1)) _=_
  rw [bar]
  rfl

theorem filed (g:ℝ)(v:∀i,(F i).Coeff)(z:I→ Cover)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
    (p:Period)(T:p.Tree):
    (∀(n:Side)(U:Config G n),measured R d g v z U=
      ∑b,WilsonOriginalPublicTrialFigure.weight R d g v b * (group R D d b κ pt z n U:ℂ)) ∧
    WilsonOriginalPublicTrialNormalization.series R d g v z p T=
      ∑b,WilsonOriginalPublicTrialFigure.weight R d g v b • WilsonPositionProgramCopyTop.normalized R p d z b T:=by
  refine ⟨fun n U=>?_,WilsonOriginalPublicTrialNormalization.filed ..⟩
  simp_rw [heard]
  exact WilsonOriginalPublicTrialFigure.opened ..

end YM.Integration.WilsonOlderFreshSoftTrialOpening
end
