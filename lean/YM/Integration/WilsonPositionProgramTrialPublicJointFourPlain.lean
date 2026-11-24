import YM.Integration.WilsonPositionProgramTrialPublicJointFourBoard
import YM.Integration.WilsonOriginalPublicNodalPlainSensor

/-! The measured public field through weight four has one shape-independent nonconstant finite section. All other test votes are scalar on the actual tree. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourPlain
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

theorem positive {h:ℕ}(F:Frame G h)(simple:G.Simple)(cap:h ≤ 4)(a:Alma F)
    (active:rankS (notar F a)≠0):sheet F a=0:=by
  by_contra nonunit
  have size:=(F.factors_pos (sheet F a) nonunit)
  have noOne:=WilsonMaxwellThermometerWardColors.arity simple F (sheet F a)
  have cost:=WilsonMaxwellThermometerChargedHeads.graded F (sheet F a)
  have limit:((F.grades (sheet F a)).1)+rankS (notar F a) ≤ h:=a.property
  omega

theorem scalar (i:Fin (n+1))(z:Lattice.Cover):printed R W Y true (d i) z 0=1:=by
  simp only [printed,if_true,(F_ i).starts_unit]
  change MvPolynomial.aeval _ 1=1
  exact map_one _

theorem axis (K:ℕ)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(a:Alma (F_ i))
    (simple:G.Simple)(cap:d i ≤ 4):
    printed R W Y true (d i) (z i) (sheet (F_ i) a)=positioned R W d Y z i K a:=by
  have src:=WilsonOriginalPublicFigureWick.priced_word W (F_ i) (site Y z) (R.family.S.a K)
    (R.family.S.a_pos K).ne' (chartV (site Y z) i) (ray R d i a)
  rw [WilsonPositionProgramTrialPublicJointFourHorizons.original R W simple cap,
    WilsonPositionProgramTrialPublicJointFourShell.original _ simple cap,map_zero,add_zero,add_zero] at src
  simpa only [printed,if_true,WilsonPositionProgramTrialPublicJointSourceProjected.label,positioned,WilsonPositionProgramTrialPublicJointSourceProjected.ray,LinearEquiv.symm_apply_apply,site,
    chartV,Function.comp_apply] using src

def modal (c:Source R d)(i:Fin (n+1))(a:Alma (F_ i)):PowerSeries ℂ:=
  if rankS (notar (F_ i) a)=0 then complex (c i a) else 0

def principal (c:Source R d)(K:ℕ)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1)):Paper:=
  ∑a,Bare.scalar Tr (modal R d c i a)*positioned R W d Y z i K a

def counter (c:Source R d)(ξ:Disp n)(i:Fin (n+1))(z:Lattice.Cover):PowerSeries ℂ:=
  ∑a,if rankS (notar (F_ i) a)=0 then 0 else money R d D cut T x y σ sp o c ξ i z a

def value (ξ:Disp n)(i:Fin (n+1))(z:Lattice.Cover):ℝ:=
  fee R d D cut T x y σ sp o ξ i z (plain (F_ i) 0)

theorem weight (ξ:Disp n)(i:Fin (n+1))(z:Lattice.Cover)(a:Alma (F_ i))(live:rankS (notar (F_ i) a)=0):
    fee R d D cut T x y σ sp o ξ i z a=value R d D cut T x y σ sp o ξ i z:=by
  rw [WilsonOriginalPublicNodalPlainSensor.only (F_ i) a live]
  simp only [fee,value,WilsonOriginalPublicNodalPlainSensor.chosen]

theorem original (simple:G.Simple)(c:Source R d)(K:ℕ)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))
    (cap:d i ≤ 4):
    field R W (fun _=>true) d D cut Y T x y σ sp o c ξ i (z i)=
      Bare.scalar Tr (PowerSeries.C (value R d D cut T x y σ sp o ξ i (z i):ℂ))*principal R W d Y c K z i+
      Bare.scalar Tr (counter R d D cut T x y σ sp o c ξ i (z i)):=by
  unfold field principal counter
  simp only [Bare.scalar,map_sum,Finset.mul_sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ordinary:rankS (notar (F_ i) a)=0
  · simp only [ordinary,if_pos,modal,map_zero,add_zero]
    rw [WilsonPositionProgramTrialPublicJointFirstFibre.money,weight R d D cut T x y σ sp o ξ i (z i) a ordinary,map_mul,
      axis R W d Y K z i a simple cap,mul_assoc]
  · simp only [modal,if_neg ordinary,map_zero,zero_mul,mul_zero,zero_add,
      positive (F_ i) simple cap a ordinary,scalar,mul_one]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourPlain
