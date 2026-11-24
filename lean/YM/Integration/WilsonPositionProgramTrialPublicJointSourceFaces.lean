import YM.Integration.WilsonPositionProgramTrialPublicJointSourceProjected

/-! The exact signed residues on each occupied face of the actual corrected
source, at the measured clock through degree two. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceFaces
open RG Lattice Wilson Tree Labels XSpace XSpace.Cirrus XSpace.Rose XSpace.Normalize PowerSeries Finset Precision
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard PhysicalNext.Repeat.Legato
open WilsonOriginalPublicNodalBufferedCellRow (Source)
open WilsonOriginalPublicNodalBufferedCellFilm (Disp)
open WilsonPositionProgramTrialPublicJointFirstFibre (field)
open WilsonPositionProgramTrialPublicJointSourceProjected (average positioned lower invisible input)
open WilsonPositionProgramTrialPublicJointSecondScore (firstWeight secondWeight ground)
open WilsonIndependentSpoutMasterOrbitClock (measure)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
  (Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)(y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→CellR)
  (m K:ℕ)(b:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)
local notation "Tr" => W.tree Y.F.p
local notation "Paper" => Bare.Series Tr G
local notation "inc" => input R W d D cut m K b
local notation "heard" => average R W d D cut Y T x y σ sp o inc ξ z
local notation "native" => field R W (fun _=>true) d D cut Y T x y σ sp o inc ξ
local notation "pure_" i:arg => heard i (positioned R W d Y z i K)
local notation "refund_" i:arg => heard i (lower R W d Y z i)+heard i (invisible R W d Y z i)

def sector (S B:Finset (Fin (n+1))):Paper:=
  (∏i∈B,(refund_ i))*(∏i∈S\B,(pure_ i))

theorem word (S:Finset (Fin (n+1))):
    (∏i∈S,native i (z i))-(∏i∈S,(pure_ i))=
    ∑B∈S.powerset.erase ∅,sector R W d D cut Y T x y σ sp o m K b ξ z S B:=by
  let f:=sector R W d D cut Y T x y σ sp o m K b ξ z S
  have one (i:Fin (n+1)):native i (z i)=(refund_ i)+(pure_ i):=by
    rw [WilsonPositionProgramTrialPublicJointSourceProjected.original];abel
  have blank:f ∅=∏i∈S,(pure_ i):=by simp only [f,sector,prod_empty,sdiff_empty,one_mul]
  have stock:(∏i∈S,native i (z i))=∑B∈S.powerset,f B:=by
    simp_rw [one]
    rw [Finset.prod_add]
    rfl
  have all:=sum_erase_add S.powerset f (show ∅∈S.powerset by simp)
  rw [stock,←blank,←all,add_sub_cancel_right]

theorem original (B:PowerSeries ℝ)(unit:constantCoeff B=1)(S:Finset (Fin (n+1))):
    let raw:=∏i∈S,native i (z i)
    let paid:=∏i∈S,(pure_ i)
    let N:=Bare.normalized Tr G
    let soft:=Next.Rank.Normal.blend (Bare.Q Tr G) 0
    let first:=soft (firstWeight Tr G)
    let second:=soft (secondWeight Tr G)
    coeff 2 (measure B (N raw))-coeff 2 (measure B (N paid))=
      ∑s∈S.powerset.erase ∅,let P:=sector R W d D cut Y T x y σ sp o m K b ξ z S s
        WilsonPositionProgramTrialPublicJointSecondScore.next Tr G P-first*coeff 1 (N P)-
          second*ground Tr G P+(coeff (R:=ℝ) 1 B:ℂ)*coeff 1 (N P):=by
  intro a p N soft s1 s2
  rw [WilsonPositionProgramTrialPublicJointSecondScore.reported Tr G B unit a p]
  have delta:=word R W d D cut Y T x y σ sp o m K b ξ z S
  change a-p=_ at delta
  rw [delta]
  simp only [map_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply sum_congr rfl
  intro t _
  rw [WilsonPositionProgramTrialPublicJointSecondScore.raw]

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceFaces
