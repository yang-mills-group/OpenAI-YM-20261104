import YM.Integration.WilsonIndependentMatchedTopReceipt
import YM.Integration.WilsonIndependentMatchedFiledAtSix

/-! Held numerical values of the whole finite residual. The scalar multiplying
the complete compensated difference acts only after its two group fields
have been assembled, including the full grade-six matching verse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopCounterterm
open WilsonCoeffUV WilsonCoeffUV.Shard
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08 Wilson Tree PowerSeries
open Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open XSpace XSpace.Cirrus PhysicalNext.Repeat.Legato FVA2
open WilsonIndependentMatchedNamedPair (sectionAt placed)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedTopReceipt (realDose)
open scoped BigOperators Topology Classical
variable {G:Gauge}{d D k u e:ℕ}(R:Run G)(I:Initialize G)(Y:Sample 2)
local notation "F" d:max => R.family.labels.level d
local notation "rnk" h:max => WilsonPositionProgramMasterBirth.rank R (d:=h)

def read (n:Side)(b:Volume D)(P:TowerS G D) : Ink (Woods G n) := flash (jot b (P.1 n))

private theorem times (n:Side)(b:Volume D)(t:ℝ){P:TowerS G D}(ok:On k P) :
    read n b (t • P)=t • read n b P := by
  change flash (jot b (t • P.1 n))=_
  rw [map_smul,flash_mu t (jot_length b (ok.launch n))]
  rfl

private theorem minus (n:Side)(b:Volume D){P Q:TowerS G D}(ok:On k P)(other:On k Q) :
    read n b (P-Q)=read n b P -read n b Q := by
  change flash (jot b (P.1 n-Q.1 n))=_
  rw [map_sub,flash_sub (finite_shell (jot_length b (ok.launch n))) (finite_shell (jot_length b (other.launch n)))]
  rfl

def polynomial (survey:Bool)(i:Fin 2)(w:d<D)(v:Verse (F d))(b:Volume D) : Ink (Woods G Y.F.p.side) :=
  ∑ s,X^(rnk d-valence (F d) s) * Blue.soil (realDose R (w:=w) b v s) *
    jet (fun a=>placed R I Y survey d (Y.layout i) (sheet (F d) s)
      (translate (-(chartV Y i)) (mantle a)))

theorem actual (survey:Bool)(i:Fin 2)(w:d<D)(v:Verse (F d))(b:Volume D) :
    X^(rnk d)*read Y.F.p.side b (Shrine (plate (sectionAt R I survey d) w) v) =
      polynomial R I Y survey i w v b := by
  have head :
      X^(rnk d)*read Y.F.p.side b (Shrine (plate (sectionAt R I survey d) w) v) =
        ∑ s,X^(rnk d-valence (F d) s)*Blue.soil (v s)*
          (jewelBloom w s b • jet (Plies (sectionAt R I survey d) (sheet (F d) s) Y.F.p.side)) := by
    cases survey with
    | false =>
      have fit:=WilsonPositionProgramMasterBirth.assembly R w 0 Y.F.p.side v b
      rw [Peak_initial] at fit
      exact fit
    | true =>
      have fit:=WilsonMaxwellThermometerSurveyBirth.assembly R I w 0 Y.F.p.side v b
      rw [Peak_initial] at fit
      exact fit
  rw [head,polynomial]
  refine Finset.sum_congr rfl (fun s _=>?_ )
  rw [←WilsonIndependentMatchedTopFilm.recentered,realDose,map_mul]
  simp only [Blue.soil,PowerSeries.map_C,Algebra.smul_def]
  have scale (x:ℝ) : algebraMap ℝ (Ink (Woods G Y.F.p.side)) x=PowerSeries.C (MvPolynomial.C x) := by
    rw [IsScalarTower.algebraMap_apply ℝ (POL (Woods G Y.F.p.side)) (Ink (Woods G Y.F.p.side)),MvPolynomial.algebraMap_eq]
    rfl
  rw [scale]
  ring

/-- The entire grade-six stable field, restored in one step at the top
selected by the common dated purchase. -/
theorem restored (low high:Bool)(i:Fin 2)(w:6<D){H:Hol G}{v:Rails 6 k u e}{E W K U:Credit}
    (L:CutsP H (sectionAt R I high 6) w v E W K U)(top:L.N=L.ceilC)
    (c4:Verse (F 4))(δ c:ℝ)(positive:0<δ)
    (input:L.pt=δ^2 • Shrine (plate (sectionAt R I low 4) (show 4<D by omega)) c4)
    (b:Volume D) :
    let n:=Y.F.p.side
    let peak:=max (rnk 4) (rnk 6)
    X^peak*read n b ((c*(δ^2)⁻¹) • L.springP L.i) =
      c • (X^(peak-rnk 4)*polynomial R I Y low i (show 4<D by omega) c4 b) -
      (c*(δ^2)⁻¹) • (X^(peak-rnk 6)*polynomial R I Y high i w L.tileP b) := by
  let w4:4<D:=by omega
  let P:=Shrine (plate (sectionAt R I low 4) w4) c4
  let Q:=Shrine L.Ntop L.tileP
  let n:=Y.F.p.side
  let t:=c*(δ^2)⁻¹
  let peak:=max (rnk 4) (rnk 6)
  have okP:On k P := by
    obtain ⟨_,_,all⟩:=WilsonIndependentMatchedFiledIncome.named R I low 4 w4
      ((by decide : 4≤6).trans v.hk) e u
    exact (all c4).1
  have okQ:On k Q := by
    obtain ⟨_,_,all⟩:=WilsonIndependentMatchedFiledIncome.named R I high 6 w v.hk e u
    rw [show Q=Shrine (plate (sectionAt R I high 6) w) L.tileP by
      unfold Q plate; rw [WilsonIndependentMatchedTopStencils.initial L top]]
    exact (all L.tileP).1
  have undo:t*δ^2=c:=by dsimp [t]; field_simp
  have state:t • L.springP L.i = c • P-t • Q := by
    rw [L.carve1,input,smul_sub,smul_smul,undo]
  have hP:X^peak*read n b P=
      X^(peak-rnk 4)*polynomial R I Y low i w4 c4 b := by
    rw [←actual R I Y]
    rw [←mul_assoc,←pow_add,Nat.sub_add_cancel (Nat.le_max_left ..)]
  have hQ:X^peak*read n b Q=
      X^(peak-rnk 6)*polynomial R I Y high i w L.tileP b := by
    have h:X^(rnk 6)*read n b Q=polynomial R I Y high i w L.tileP b:=
      WilsonIndependentMatchedTopReceipt.original R I Y high L top i b
    rw [←h,←mul_assoc,←pow_add,Nat.sub_add_cancel (Nat.le_max_right ..)]
  change X^peak * read n b (t • L.springP L.i) = _
  rw [state,minus n b (okP.μ c) (okQ.μ t),times n b c okP,times n b t okQ,mul_sub,
    mul_smul_comm,mul_smul_comm,hP,hQ]

end YM.Integration.WilsonIndependentMatchedTopCounterterm
