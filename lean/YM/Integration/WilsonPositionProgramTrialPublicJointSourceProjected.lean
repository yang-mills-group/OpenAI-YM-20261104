import YM.Integration.WilsonPositionProgramTrialPublicJointFirstFibre
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceVote
import YM.Integration.WilsonPositionProgramTrialPublicJointPositionInlet
import YM.Integration.WilsonPositionProgramTrialPublicJointSecondScore

/-! The measured chart at each Fourier/cell seat, with independent terms for the
compact gauge null and the lower-horizon change on its actual surveyed tree. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceProjected
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

def ray (i:Fin (n+1))(a:Alma (F_ i)):(F_ i).Coeff:=(F_ i).coords ((F_ i).basis (sheet (F_ i) a))

def input (m K:ℕ)(b:Source R d):Source R d:=fun i=>refill R W d D cut m K i (b i)

def label (z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(K:ℕ)(a:Alma (F_ i)):Sec G (d i):=
  received (site Y z) (R.family.S.a K) ((R.family.S.a K:ℂ)^(d i) • project W (F_ i) (ray R d i a))

def average (c:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))
    (bank:Alma (F_ i)→Paper):Paper:=
  ∑a,Bare.scalar (W.tree Y.F.p) (money R d D cut T x y σ sp o c ξ i (z i) a)*bank a

def positioned (z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(K:ℕ)(a:Alma (F_ i)):Paper:=
  regal W (d i) (site Y z) (chartV (site Y z) i) (label R W d Y z i K a)

def lower (z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(a:Alma (F_ i)):Paper:=
  superior W (F_ i) (site Y z) (chartV (site Y z) i) (ray R d i a)

def invisible (z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(a:Alma (F_ i)):Paper:=
  Bare.column (W.tree Y.F.p) (W.surveys (d i)) (chartV (site Y z) i) (remainder W (F_ i) (ray R d i a))

theorem original (m K:ℕ)(b:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1)):
    let c:=input R W d D cut m K b
    let heard:=average R W d D cut Y T x y σ sp o c ξ z i
    field R W (fun _=>true) d D cut Y T x y σ sp o c ξ i (z i)=
      heard (positioned R W d Y z i K)+heard (lower R W d Y z i)+heard (invisible R W d Y z i):=by
  intro c heard
  change (∑a:Alma (F_ i),Bare.scalar _ _*printed R W Y true (d i) (z i) (sheet (F_ i) a))=_
  dsimp only [heard,average]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [←mul_add,←mul_add]
  congr 1
  have src:=WilsonOriginalPublicFigureWick.priced_word W (F_ i) (site Y z) (R.family.S.a K)
    (R.family.S.a_pos K).ne' (chartV (site Y z) i) (ray R d i a)
  simpa only [printed,if_true,label,lower,positioned,invisible,ray,LinearEquiv.symm_apply_apply,site,chartV,
    Function.comp_apply] using src

def datum (m K:ℕ)(b:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(q:ℕ):Sec G (d i):=
  ∑a,coeff q (money R d D cut T x y σ sp o (input R W d D cut m K b) ξ i (z i) a) • label R W d Y z i K a

/-- Reconstruct the actual finite series of public labels at each order.
This combines the entering thermal coefficient and the lower-grade engineering
read before taking any joint proper face. -/
theorem coefficient (m K:ℕ)(b:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1))(q:ℕ):
    let c:=input R W d D cut m K b
    let gross:=average R W d D cut Y T x y σ sp o c ξ z i (positioned R W d Y z i K)
    let p:=datum R W d D cut Y T x y σ sp o m K b ξ z i
    coeff q gross=∑t∈Finset.HasAntidiagonal.antidiagonal q,
      coeff t.2 (regal W (d i) (site Y z) (chartV (site Y z) i) (p t.1)):=by
  intro c gross p
  simp only [gross,average,map_sum,coeff_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [p,datum,map_sum,map_smul,positioned]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Bare.scalar,coeff_map,PowerSeries.coeff_smul,c];rw [Algebra.smul_def];rfl

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceProjected
