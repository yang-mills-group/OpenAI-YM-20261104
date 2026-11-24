import YM.Integration.WilsonOriginalPublicTrialPhaseFiling
import YM.Integration.WilsonAddressedFiniteGuardCapital

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyBirthGross
open Finset Lattice RG Source Labels Push.Local Extra.Multi Push.AbsoluteSums.Animals
open PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicEntranceOpticalUnits (dye rank)
open WilsonPositionProgramBlockedTrialAddBack (names)
open private material from YM.Integration.WilsonAddressedFiniteGuardCapital
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){K N p:ℕ}
local notation "C" => R.family
local notation "P" => (C).path.rep N p K
local notation "H" => (C).path.levels.clock.hatBeta K

def ink (d:ℕ)(z:ℝ):ℝ:=Real.exp ((z+2)*(atomTiles ((C).localSection d):ℝ))*dye R d

theorem original (live:K≤N)(d:ℕ)(o:Site ((C).side K p))(v:(C).label d)
    {z:ℝ}(support:((C).path.levels.budget K).supportExponent≤z):
    let S:=(C).localSection d
    let F:=(C).labels.level d
    let D:=S.footprint o
    let κ:=(C).path.levels.clock.forcedAllowance K
    let M:=BasisCost.price S*F.coeffSize (names R d N p K v)
    let T:=ink R d z*H^(rank R d)*F.coeffSize v
    0≤WilsonOriginalPublicTrialPhaseFiling.reserve R d o v (N:=N) ∧
      WilsonOriginalPublicTrialPhaseFiling.reserve R d o v (N:=N)≤T ∧
      (Real.sqrt κ≤1 → (P).p.mass D 0+2*(D.card:ℝ)*Real.sqrt κ*(P).p.mass D M≤
        2*(S.stencil.card:ℝ)*T):=by
  intro S F D κ M T
  have date:(P).p=(C).path.levels.budget K:=(R.makes.wilson.represents N p K live).vac
  have zs:(P).p.supportExponent≤z:=by rwa [date]
  have budget:=WilsonAddressedFiniteGuardFields.budget R (fun _:Unit=>d) N p K (fun _=>v) live ()
  have sz:0≤F.coeffSize v:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have mp:0≤M:=mul_nonneg (zero_le_one.trans (BasisCost.price_pos S)) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  have mcost:M≤dye R d*H^(rank R d)*F.coeffSize v:=
    ((le_add_of_nonneg_left (norm_nonneg (v 0))).trans budget).trans
      (mul_le_mul_of_nonneg_right (material R d K) sz)
  have tiles:(coverNumber (P).p.B D:ℝ)≤(atomTiles S:ℝ):=by exact_mod_cast atomTiles_price S (P).p o
  have extra:0≤z+2:=by linarith [(P).p.exponent_pos]
  have expBound:Real.exp (((P).p.supportExponent+2)*(coverNumber (P).p.B D:ℝ)) ≤
      Real.exp ((z+2)*(atomTiles S:ℝ)):=by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (by linarith only [zs] : (P).p.supportExponent+2≤z+2) (by positivity)).trans
      (mul_le_mul_of_nonneg_left tiles extra)
  have rp:0≤reservedMass (P).p D M:=mul_nonneg (Real.exp_pos _).le mp
  have bound:reservedMass (P).p D M≤T:=by
    dsimp only [reservedMass,T,ink]
    calc _≤Real.exp ((z+2)*(atomTiles S:ℝ))*(dye R d*H^(rank R d)*F.coeffSize v):=
            mul_le_mul expBound mcost mp (Real.exp_pos _).le
         _=_:=by ring
  refine ⟨rp,bound,?_⟩
  intro small
  have mass:(P).p.mass D M≤reservedMass (P).p D M:=by
    apply mul_le_mul_of_nonneg_right _ mp
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith : (P).p.supportExponent≤(P).p.supportExponent+2) (by positivity)
  have card:(D.card:ℝ)≤(S.stencil.card:ℝ):=by exact_mod_cast Finset.card_image_le
  have mb:0≤(P).p.mass D M:=mul_nonneg (Real.exp_pos _).le mp
  have cb:0≤2*(D.card:ℝ):=by positivity
  simp only [BudgetPoint.mass,mul_zero,zero_add]
  change 2*(D.card:ℝ)*Real.sqrt κ*(P).p.mass D M≤2*(S.stencil.card:ℝ)*T
  calc _≤(2*(D.card:ℝ)*1)*(P).p.mass D M:=mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left small cb) mb
       _≤2*(S.stencil.card:ℝ)*T:=by
           rw [mul_one]
           exact mul_le_mul (by linarith) (mass.trans bound) mb (by positivity)
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyBirthGross
end
