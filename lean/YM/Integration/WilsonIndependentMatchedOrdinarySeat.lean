import YM.Integration.WilsonIndependentMatchedOrdinaryRay
import YM.Integration.WilsonIndependentMatchedTopCounterterm
import YM.Integration.WilsonIndependentMatchedFiledIncome

/-! The complete finite section on a torus has its genuinely filed ordinary
radial series at each translated site and for each of its derivative tests. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedOrdinarySeat
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08
open Wilson Tree Precision AnalyticNext.QuarticMatch.Sheets Exterior Next.Free
open Gauge Source Labels XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open PertExtension RegulatorIR RegulatorIR.Halo PowerSeries
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open WilsonIndependentMatchedOrdinaryRay (group)
open scoped Classical BigOperators ContDiff
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){d D:ℕ}
local notation "F" => R.family.labels.level d

def here (n:Side)(v:TreeVars G n): Ink (Woods G n) →+* Cost:=
  PowerSeries.map (MvPolynomial.eval v)

theorem ground (n:Side)(v:TreeVars G n)(a:Cost):here n v (Blue.soil a)=a:=by
  ext1 h
  simp only [here,Blue.soil,coeff_map,MvPolynomial.eval_C]

theorem moved {n:Side}(M:Matrix (Woods G n) (Woods G n) ℝ)(v:TreeVars G n)(A:Ink (Woods G n)):
    here n v (loom M A)=here n (M*ᵥv) A:=by
  ext1 e
  simp only [here,loom,coeff_map]
  exact cord_apply M v _

theorem weighted {n:Side}(s:Bool)(a:(F).Index)(o:Cover)(v:TreeVars G n):
    let h:=((F).grades a).2
    here n (spear (jog (wrap n o):Woods G n≃Woods G n)*ᵥv) (jet (Plies (sectionAt R W s d) a n))=
      X^h*shelter h (WilsonIndependentRawNamedStencil.shifted R W s d a o) (sample v):=by
  dsimp only
  rw [WilsonIndependentMatchedOrdinaryRay.original R W s a o v]
  have smooth:Green (Plies (sectionAt R W s d) a n):=by
    cases s with
    | false=>exact innu _ _ (R.makes.sections d) a n
    | true=>exact innu _ W.hol (WilsonOriginalPivotWardSurvey.issued R W d).1 a n
  rw [here,WilsonIndependentMatchedOrdinaryRay.evaluate _ smooth]
  apply congrArg RegulatorIR.Prim.tale
  funext t
  rw [WilsonIndependentMatchedOrdinaryRay.moved R W s a o (t • v),Matrix.mulVec_smul]

def received {n:Side}(s:Bool)(w:d<D)(b:Volume D)(c:Verse F)(o:Cover)(v:TreeVars G n):Cost:=
  ∑a, realDose R (w:=w) b c a*
      shelter (valence F a) (WilsonIndependentRawNamedStencil.shifted R W s d (sheet F a) o) (sample v)

theorem top (s:Bool)(w:d<D)(b:Volume D)(c:Verse F)(n:Side):
    X^WilsonPositionProgramMasterBirth.rank R (d:=d)*
      flash (jot b ((Shrine (plate (sectionAt R W s d) w) c).1 n))=
      ∑a,X^(WilsonPositionProgramMasterBirth.rank R (d:=d)-valence F a)*
        Blue.soil (realDose R (w:=w) b c a)*jet (Plies (sectionAt R W s d) (sheet F a) n):=by
  have head:X^WilsonPositionProgramMasterBirth.rank R (d:=d)*
      flash (jot b ((Shrine (plate (sectionAt R W s d) w) c).1 n))=
    ∑a,X^(WilsonPositionProgramMasterBirth.rank R (d:=d)-valence F a)*Blue.soil (c a)*
       (jewelBloom w a b • jet (Plies (sectionAt R W s d) (sheet F a) n)):=by
    cases s with
    | false=>
      have h:=WilsonPositionProgramMasterBirth.assembly R w 0 n c b
      rw [Peak_initial] at h
      exact h
    | true=>
      have h:=WilsonMaxwellThermometerSurveyBirth.assembly R W w 0 n c b
      rw [Peak_initial] at h
      exact h
  rw [head]
  apply Finset.sum_congr rfl
  intro a _
  rw [realDose,map_mul]
  simp only [Blue.soil,PowerSeries.map_C,Algebra.smul_def]
  have scalar (t:ℝ):algebraMap ℝ (Ink (Woods G n)) t=PowerSeries.C (MvPolynomial.C t):=by
    rw [IsScalarTower.algebraMap_apply ℝ (POL (Woods G n)) (Ink (Woods G n)),MvPolynomial.algebraMap_eq]
    rfl
  rw [scalar];ring

theorem original {n:Side}(s:Bool)(w:d<D)(b:Volume D)(c:Verse F)(o:Cover)(v:TreeVars G n):
    let T:=Shrine (plate (sectionAt R W s d) w) c
    here n v (flash (skewV (wrap n o) (jot b (T.1 n))))=received R W s w b c o v:=by
  dsimp only
  let M:=spear (jog (wrap n o):Woods G n≃Woods G n)
  let r:=WilsonPositionProgramMasterBirth.rank R (d:=d)
  have ⟨_,_,paid⟩:=WilsonIndependentMatchedFiledIncome.named R W s d w le_rfl 0 0
  let T:=Shrine (plate (sectionAt R W s d) w) c
  have ok:On d T:=(paid c).1
  rw [translate_value n (wrap n o) _ (jot_length b (ok.launch n)),moved]
  change here n (M*ᵥv) (flash (jot b (T.1 n)))=_
  apply mul_left_cancel₀ (pow_ne_zero r (PowerSeries.X_ne_zero (R:=ℝ)))
  have hm:here n (M*ᵥv) PowerSeries.X=PowerSeries.X:=by simp [here]
  have h:=congrArg (here n (M*ᵥv)) (top R W s w b c n)
  simp only [map_mul,map_pow,hm,map_sum,ground] at h
  rw [h,received,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have he:=weighted R W s (sheet F a) o v
  change here n (M*ᵥv) _=X^(valence F a)*_ at he
  rw [he]
  have le:valence F a≤r:=Finset.le_sup (f:=valence F) (Finset.mem_univ a)
  change X^(r-valence F a)* _*(X^(valence F a)*_) = X^r*_
  rw [show X^r=(X^(r-valence F a)*X^valence F a:PowerSeries ℝ) from
         ((pow_add _ _ _).symm.trans (congrArg (fun j:ℕ=>(X:PowerSeries ℝ)^j) (Nat.sub_add_cancel le))).symm]
  ring_nf
  rfl

end YM.Integration.WilsonIndependentMatchedOrdinarySeat
