import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyCutoffRoom
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyBirthGross
/-! The cutoff salaries of the actual uncut fields on the N vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopySeedFare
open Finset Real Wilson Lattice RG Source Labels Extra.Multi PhysicalNext.Repeat.Legato
open WilsonOriginalPublicTrialPhaseFiling (reserve)
open WilsonOriginalPublicTrialPhaseRate (wage)
open WilsonMeasuredPublicEntranceTransferCopyBirthGross (ink)
open WilsonMeasuredPublicEntranceTransferCopyCutoffRoom (tariff)
open WilsonOriginalMicroscopicEntranceOpticalUnits (dye rank)
open WilsonPositionProgramBlockedTrialAddBack (names)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){K N p:ℕ}
local notation "C" => R.family
local notation "P" => (C).path.rep N p K
local notation "H" => (C).path.levels.clock.hatBeta K

def capital (d load:ℕ)(z T:ℝ):ℝ:=
  let X:=ink R d z*T
  1+T+2*((C).localSection d).stencil.card*X+tariff load*(1+X)

theorem original (live:K≤N)(d load:ℕ)(o:Site ((C).side K p))(v:(C).label d)
    {z T:ℝ}(tp:0≤T)(e:ℕ)(support:((C).path.levels.budget K).supportExponent≤z)
    (source:((C).labels.level d).coeffSize v≤T*H^e):
    let S:=(C).localSection d
    let F:=(C).labels.level d
    let D:=S.footprint o
    let κ:=(C).path.levels.clock.forcedAllowance K
    let M:=BasisCost.price S*F.coeffSize (names R d N p K v)
    let B:=capital R d load z T*H^(16+(rank R d+e))
    1≤B ∧ F.coeffSize v≤B ∧
      (P).p.mass D 0+2*(D.card:ℝ)*sqrt κ*(P).p.mass D M≤B ∧
      (wage (P).p.B load (reserve R (N:=N) d o v))⁻¹≤B:=by
  intro S F D κ M B
  let X:=ink R d z*T
  let k:=rank R d+e
  have one:1≤H:=((C).path.levels.fits.delayed K).le
  have hp:0≤H:=zero_le_one.trans one
  have k1:1≤H^k:=one_le_pow₀ one
  have bp:1≤H^(16+k):=one_le_pow₀ one
  have μp:0≤ ink R d z:=mul_nonneg (exp_pos _).le (by
    dsimp only [dye];linarith [BasisCost.price_pos S])
  have xp:0≤X:=mul_nonneg μp tp
  have pt:0≤tariff load:=by unfold tariff;positivity
  let buy:=WilsonMeasuredPublicEntranceTransferCopyBirthGross.original R live d o v support
  have money:ink R d z*H^(rank R d)*F.coeffSize v≤X*H^k:=by
    calc _≤ ink R d z*H^(rank R d)*(T*H^e):=mul_le_mul_of_nonneg_left source (by positivity)
         _=_:=by dsimp only [X,k];rw [pow_add];ring
  have sq:sqrt κ≤1:=by
    have small:κ≤1:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
    simpa using sqrt_le_sqrt small
  have seed:0≤2*(S.stencil.card:ℝ)*X:=by positivity
  have top:0≤tariff load*(1+X):=by positivity
  have C0:1≤capital R d load z T:=by change 1≤1+T+2*(S.stencil.card:ℝ)*X+tariff load*(1+X);linarith
  have rk:H^k≤H^(16+k):=pow_le_pow_right₀ one (by omega)
  have re:H^e≤H^(16+k):=pow_le_pow_right₀ one (by dsimp only [k];omega)
  refine ⟨one_le_mul_of_one_le_of_one_le C0 bp,?_,?_,?_⟩
  · exact source.trans (mul_le_mul (by
      change T≤1+T+2*(S.stencil.card:ℝ)*X+tariff load*(1+X);linarith) re (by positivity) (zero_le_one.trans C0))
  · refine (buy.2.2 sq).trans ((mul_le_mul_of_nonneg_left money (by positivity)).trans ?_)
    rw [←mul_assoc]
    exact mul_le_mul (by change 2*(S.stencil.card:ℝ)*X≤1+T+2*(S.stencil.card:ℝ)*X+tariff load*(1+X);linarith)
      rk (by positivity) (zero_le_one.trans C0)
  · have sale:=WilsonMeasuredPublicEntranceTransferCopyCutoffRoom.original R (p:=p) live load
      (reserve R (N:=N) d o v)
    rw [abs_of_nonneg buy.1] at sale
    refine sale.trans ?_
    have r:=buy.2.1.trans money
    have q:1+reserve R (N:=N) d o v≤(1+X)*H^k:=by nlinarith only [r,k1]
    calc _≤tariff load*H^16*((1+X)*H^k):=mul_le_mul_of_nonneg_left q (by positivity)
         _=(tariff load*(1+X))*H^(16+k):=by rw [pow_add];ring
         _≤B:=by
           apply mul_le_mul_of_nonneg_right _ (by positivity)
           change tariff load*(1+X)≤1+T+2*(S.stencil.card:ℝ)*X+tariff load*(1+X)
           linarith
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopySeedFare
end
