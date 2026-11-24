import YM.Integration.WilsonPositionProgramTrialPublicJointFourDatum

/-! Centering the full measured weight-four source on the actual finite Wilson vacuum. The five ordinary partitions retain the same incoming source and signed test weights. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourConnected
open RG Lattice Wilson Tree Source Labels XSpace XSpace.Cirrus PowerSeries Finset Precision
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard PhysicalNext.Repeat.Legato WilsonIndependentRawRosterWord
open WilsonIndependentSpoutRosterCashier (complex)
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonIndependentMatchedNamedPair (printed)
open WilsonOriginalPublicNodalBufferedCellRow (Stamps Source gain bank profile)
open WilsonOriginalPublicNodalBufferedCellFilm (Sites Seats Disp full entry paper)
open WilsonPositionProgramTrialPublicCellHull (hull)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
  (Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)(y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→CellR)
local notation "F_" i:max => R.family.labels.level (d i)

open XSpace.Rose XSpace.Normalize
open WilsonPositionProgramSubmittedCoordinates (plain)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonPositionProgramTrialPublicJointFirstFibre (fee money field)
open WilsonPositionProgramTrialPublicJointFirstSource (site)
open WilsonPositionProgramTrialPublicJointSourceProjected (ray label positioned input)
open WilsonIndependentMatchedNamedPair (printed)
local notation "Tr" => W.tree Y.F.p
local notation "Paper" => Bare.Series Tr G

open WilsonPositionProgramTrialPublicJointFourPlain (value principal counter)
def center (A:Paper):Paper:=A-Bare.scalar Tr (Bare.normalized Tr G A)
def reading (A:Fin (n+1) → Paper):PowerSeries ℂ:=Bare.normalized Tr G (∏i,center (G:=G) W Y (A i))

theorem unitRead (c:PowerSeries ℂ):Bare.normalized Tr G (Bare.scalar Tr c)=c:=by
  simpa only [mul_one,Bare.normalize_unit] using Bare.normalized_scalar (G:=G) Tr c 1

theorem affine (A:Paper)(l k:PowerSeries ℂ):center W Y (Bare.scalar Tr l*A+Bare.scalar Tr k)=
    Bare.scalar Tr l*center W Y A:=by
  unfold center
  rw [map_add,Bare.normalized_scalar,unitRead W Y]
  simp only [Bare.scalar,map_add,map_mul]
  ring

theorem three (A:Fin 3 → Paper):
    let M:=Bare.normalized Tr G
    reading (n:=2) W Y A=M (A 0*A 1*A 2)-
      M (A 0)*(M (A 1*A 2))-M (A 1)*(M (A 0*A 2))-M (A 2)*(M (A 0*A 1))+
      2*M (A 0)*M (A 1)*M (A 2):=by
  intro M
  let μ i:=M (A i)
  have expand:(∏i:Fin 3,center W Y (A i))=
      A 0*A 1*A 2-Bare.scalar Tr (μ 0)*(A 1*A 2)-Bare.scalar Tr (μ 1)*(A 0*A 2)-
      Bare.scalar Tr (μ 2)*(A 0*A 1)+Bare.scalar Tr (μ 0*μ 1)*A 2+Bare.scalar Tr (μ 0*μ 2)*A 1+
      Bare.scalar Tr (μ 1*μ 2)*A 0-Bare.scalar Tr (μ 0*μ 1*μ 2):=by
    rw [Fin.prod_univ_three]
    simp only [center,μ,M,Bare.scalar,map_mul]
    ring
  unfold reading
  rw [expand]
  dsimp only [M,μ]
  simp only [map_sub,map_add,Bare.normalized_scalar,unitRead]
  ring

theorem original (simple:G.Simple)(c:Source R d)(K:ℕ)(ξ:Disp n)(z:Fin (n+1) → Lattice.Cover)
    (cap:∀i,d i ≤ 4):
    let F:=fun i=>field R W (fun _=>true) d D cut Y T x y σ sp o c ξ i (z i)
    let l:=fun i=>PowerSeries.C (value R d D cut T x y σ sp o ξ i (z i):ℂ)
    let P:=principal R W d Y c K z
    reading W Y F=(∏i,l i)*reading W Y P:=by
  intro F l P
  have cancel i:center W Y (F i)=Bare.scalar Tr (l i)*center W Y (P i):=by
    dsimp only [F,l,P]
    rw [WilsonPositionProgramTrialPublicJointFourPlain.original R W d D cut Y T x y σ sp o simple c K ξ z i (cap i),affine]
  unfold reading
  simp_rw [cancel]
  rw [prod_mul_distrib]
  have constants:(∏i,Bare.scalar (G:=G) Tr (l i))=Bare.scalar (G:=G) Tr (∏i,l i):=by
    simp only [Bare.scalar,map_prod]
  rw [constants,Bare.normalized_scalar]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourConnected
