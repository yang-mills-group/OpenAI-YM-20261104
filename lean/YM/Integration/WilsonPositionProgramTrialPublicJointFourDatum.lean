import YM.Integration.WilsonPositionProgramTrialPublicJointFourPlain
import YM.Integration.WilsonPositionProgramTrialPublicJointSourcePosition

/-! One finite measured section before choosing any positions, detectors or test shapes. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourDatum
open RG Lattice Wilson Tree Source Labels XSpace XSpace.Cirrus XSpace.Rose XSpace.Normalize PowerSeries Finset Precision
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedNamedPair (printed)
open WilsonOriginalPublicNodalBufferedCellRow (Source)
open WilsonOriginalPublicNodalBufferedCellFilm (Disp)
open WilsonPositionProgramTrialPublicJointFirstFibre (money field)
open WilsonPositionProgramTrialPublicJointFirstSource (site)
open WilsonPositionProgramTrialPublicJointSourceVote (refill)
open WilsonOriginalPublicFigureWick (project superior remainder)
open WilsonMaxwellThermometerPositionCurrency (received)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
  (Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)(y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→CellR)
local notation "F_" i:max => R.family.labels.level (d i)
local notation "Paper" => Bare.Series (W.tree Y.F.p) G

open WilsonPositionProgramTrialPublicJointFourPlain (modal principal)
open WilsonPositionProgramTrialPublicJointSourceProjected (input label positioned)
def filed (c:Source R d)(K:ℕ)(i:Fin (n+1))(q:ℕ):Sec G (d i):=
  ∑a,coeff q (modal R d c i a) • label R W d Y (fun _=>0) i K a

theorem common (c:Source R d)(K:ℕ)(i:Fin (n+1)){Y':Sample 2}(same:Y.F=Y'.F):
    filed R W d Y c K i=filed R W d Y' c K i:=by
  cases Y
  cases Y'
  cases same
  rfl

theorem coefficient (c:Source R d)(K:ℕ)(z:Fin (n+1) → Lattice.Cover)(i:Fin (n+1))(q:ℕ):
    coeff q (principal R W d Y c K z i)=∑t∈Finset.HasAntidiagonal.antidiagonal q,
      coeff t.2 (regal W (d i) (site Y z) (chartV (site Y z) i) (filed R W d Y c K i t.1)):=by
  simp only [principal,map_sum,coeff_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [filed,map_sum,map_smul,positioned]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Bare.scalar,coeff_map,PowerSeries.coeff_smul]
  rw [Algebra.smul_def]
  rfl

end YM.Integration.WilsonPositionProgramTrialPublicJointFourDatum
