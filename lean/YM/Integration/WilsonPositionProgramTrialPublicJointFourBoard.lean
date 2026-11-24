import YM.Integration.WilsonPositionProgramTrialPublicJointFourHorizons
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceFaces

/-! On the actual three-energy board the full surveyed letter is exactly the
positioned letter at its measured finite source. This holds on every proper
face, for the whole normalized series before its reporting clock is read. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourBoard
open RG Lattice Wilson Tree Labels XSpace XSpace.Cirrus XSpace.Rose XSpace.Normalize PowerSeries Finset Precision
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard PhysicalNext.Repeat.Legato
open WilsonOriginalPublicNodalBufferedCellRow (Source)
open WilsonOriginalPublicNodalBufferedCellFilm (Disp)
open WilsonPositionProgramTrialPublicJointFirstFibre (field)
open WilsonPositionProgramTrialPublicJointSourceProjected (average positioned lower invisible input)
open WilsonPositionProgramTrialPublicJointFirstSource (site)
open WilsonIndependentSpoutMasterOrbitClock (measure)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
variable (Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)(y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→CellR)
variable (m K:ℕ)(b:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)
local notation "Tr" => W.tree Y.F.p
local notation "inc" => input R W d D fit m K b
local notation "heard" => average R W d D fit Y T x y σ sp o inc ξ z
local notation "native" => field R W (fun _=>true) d D fit Y T x y σ sp o inc ξ
local notation "pure_" i:arg => heard i (positioned R W d Y z i K)

theorem leg (simple:G.Simple)(i:Fin (n+1))(cap:d i≤4):native i (z i)=pure_ i:=by
  rw [WilsonPositionProgramTrialPublicJointSourceProjected.original]
  simp only [average,lower,invisible,WilsonPositionProgramTrialPublicJointFourHorizons.original R W simple cap,
    WilsonPositionProgramTrialPublicJointFourShell.original _ simple cap,map_zero,mul_zero,sum_const_zero,add_zero]

theorem original (simple:G.Simple)(S:Finset (Fin (n+1)))(cap:∀i∈S,d i≤4):
    Bare.normalized Tr G (∏i∈S,native i (z i))=Bare.normalized Tr G (∏i∈S,(pure_ i)):=by
  apply congrArg (Bare.normalized Tr G)
  apply prod_congr rfl
  intro i hi
  exact leg R W d D fit Y T x y σ sp o m K b ξ z simple i (cap i hi)

theorem reported (simple:G.Simple)(S:Finset (Fin (n+1)))(cap:∀i∈S,d i≤4)
    (B:PowerSeries ℝ)(q:ℕ):
    coeff q (measure B (Bare.normalized Tr G (∏i∈S,native i (z i))))=
      coeff q (measure B (Bare.normalized Tr G (∏i∈S,(pure_ i)))):=by
  rw [original R W d D fit Y T x y σ sp o m K b ξ z simple S cap]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourBoard
