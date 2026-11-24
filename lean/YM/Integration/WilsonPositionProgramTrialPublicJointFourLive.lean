import YM.Integration.WilsonPositionProgramTrialPublicJointFourConnected
import YM.Integration.WilsonOriginalPublicNodalPlainSensor

/-! The measured public field through weight four has one shape-independent nonconstant finite section. All other test votes are scalar on the actual tree. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourLive
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
open WilsonPositionProgramTrialPublicJointFourPlain (modal principal scalar axis value)
open WilsonPositionProgramTrialPublicJointFourConnected (center reading)
open WilsonPositionProgramTrialPublicJointFirstSource (site)
open WilsonPositionProgramTrialPublicJointSourceProjected (ray label positioned input)
open WilsonIndependentMatchedNamedPair (printed)
local notation "Tr" => W.tree Y.F.p
local notation "Paper" => Bare.Series Tr G


theorem grades {h:ℕ}(F:Frame G h)(simple:G.Simple)(cap:h≤4)(a:Alma F)(live:sheet F a≠0):
    F.grades (sheet F a)=(4,2) ∧ rankS (notar F a)=0:=by
  have size:=F.factors_pos (sheet F a) live
  have noOne:=WilsonMaxwellThermometerWardColors.arity simple F (sheet F a)
  have cost:=WilsonMaxwellThermometerChargedHeads.graded F (sheet F a)
  have limit:((F.grades (sheet F a)).1)+rankS (notar F a)≤h:=a.property
  exact ⟨Prod.ext (by omega) (by omega),by omega⟩

def physical (c:Source R d)(K:ℕ)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1)):Paper:=
  ∑a,if sheet (F_ i) a=0 then 0 else Bare.scalar Tr (modal R d c i a)*positioned R W d Y z i K a

def unitCharge (c:Source R d)(i:Fin (n+1)):PowerSeries ℂ:=
  ∑a,if sheet (F_ i) a=0 then modal R d c i a else 0

theorem split (simple:G.Simple)(c:Source R d)(K:ℕ)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(cap:d i≤4):
    principal R W d Y c K z i=physical R W d Y c K z i+Bare.scalar Tr (unitCharge R d c i):=by
  unfold principal physical unitCharge
  simp only [Bare.scalar,map_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro a _
  by_cases h:sheet (F_ i) a=0
  · have one:positioned R W d Y z i K a=1:=by
      rw [←axis R W d Y K z i a simple cap,h,scalar R W d Y]
    simp [h,one]
  · simp [h]

theorem centered (simple:G.Simple)(c:Source R d)(K:ℕ)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(cap:d i≤4):
    center W Y (principal R W d Y c K z i)=center W Y (physical R W d Y c K z i):=by
  rw [split R W d Y simple c K z i cap]
  simpa only [Bare.scalar,map_one,one_mul] using
    WilsonPositionProgramTrialPublicJointFourConnected.affine W Y (physical R W d Y c K z i) 1 (unitCharge R d c i)

theorem stripped (simple:G.Simple)(c:Source R d)(K:ℕ)(z:Fin (n+1)→Lattice.Cover)(cap:∀i,d i≤4):
    reading W Y (principal R W d Y c K z)=reading W Y (physical R W d Y c K z):=by
  apply congrArg (Bare.normalized Tr G)
  exact prod_congr rfl fun i _=>centered R W d Y simple c K z i (cap i)

theorem original (simple:G.Simple)(c:Source R d)(K:ℕ)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)(cap:∀i,d i≤4):
    let F:=fun i=>field R W (fun _=>true) d D cut Y T x y σ sp o c ξ i (z i)
    let l:=fun i=>PowerSeries.C (value R d D cut T x y σ sp o ξ i (z i):ℂ)
    reading W Y F=(∏i,l i)*reading W Y (physical R W d Y c K z):=by
  intro F l
  exact (WilsonPositionProgramTrialPublicJointFourConnected.original R W d D cut Y T x y σ sp o simple c K ξ z cap).trans
    (congrArg (fun a:PowerSeries ℂ=>(∏i,l i)*a) (stripped R W d Y simple c K z cap))

end YM.Integration.WilsonPositionProgramTrialPublicJointFourLive
