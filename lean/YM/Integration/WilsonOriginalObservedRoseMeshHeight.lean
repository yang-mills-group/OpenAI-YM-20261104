import YM.Integration.WilsonOriginalObservedRoseMeshPurse

/-! Only one reciprocal coupling is needed for all measured inverse stretches. The engineering power is the sum of the actual occupied dimensions, even at a moving K. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseMeshHeight
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial WilsonPositionProgramReportedField
open WilsonMeasuredPublicEntrancePanel (Panel Reading charged)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open PertExtension PertExtension.LatticePT
open MergeProof.Accent Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per f K u:ℕ}
local notation "C" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin n)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}

open Extraction WilsonAddressedPhysicalCells


open Motion WilsonOriginalObservedRoseCorrectedWords
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonOriginalMicroscopicGuardedPage (full page_at)
open WilsonOriginalMicroscopicGuardedReporters (stretch)
open WilsonPositionProgramReportedField
local notation "a" i:max => R.family.S.a i
local notation "F" i:max => R.family.labels.level (d i)

open WilsonOriginalObservedRoseMeshPurse (quote)
open WilsonReceivedCanonicalVerseRegister (shoulder)
open WilsonReceivedCanonicalVersePortfolio (nonneg)

def tilt (n A:ℕ):ℝ:=((A:ℝ)+1)⁻¹ / ((n:ℝ)+1)
def variation (j N per:ℕ)(i:Fin n)(y:(C).label (d i)):ℝ:=
  |2*orbitCost (F i)*((1+WilsonOriginalMicroscopicGuardedPage.wrapCost R (d i) j)*
      Next.Rank.Spindle.paid (C) (d i) j N per y)|

def height (S:Finset (Fin n)):ℕ:=∑i:S,d i

private theorem column (A j K N per:ℕ)(i:Fin n)(y:(C).label (d i)){z:ℝ}(large:1≤z)
    (mesh:a j/a K≤z^A):
    quote R d (tilt n A) j K N per i y≤
      variation R d j N per i y*z^(A*d i)*Real.exp (Real.log z/((n:ℝ)+1)):=by
  have zp:0<z:=zero_lt_one.trans_le large
  have m:0<a j/a K:=div_pos ((C).S.a_pos j) ((C).S.a_pos K)
  have way:Real.log (a j/a K)=(C).S.scale K-(C).S.scale j:=by
    rw [Real.log_div ((C).S.a_pos _).ne' ((C).S.a_pos _).ne'];simp only [Schedule.scale,Real.log_inv];ring
  have travel:=Real.log_le_log m mesh
  rw [way,Real.log_pow] at travel
  have t:0≤tilt n A:=by unfold tilt;positivity
  have stretchPrice:tilt n A*((C).S.scale K-(C).S.scale j)≤Real.log z/((n:ℝ)+1):=calc
    _≤tilt n A*(((A:ℝ)+1)*Real.log z):=mul_le_mul_of_nonneg_left (by linarith [Real.log_nonneg large]) t
    _=_:=by unfold tilt;field_simp
  let b:=2*orbitCost (F i)*((1+WilsonOriginalMicroscopicGuardedPage.wrapCost R (d i) j)*Next.Rank.Spindle.paid (C) (d i) j N per y)
  have face:(a j/a K)^d i≤z^(A*d i):=by rw [pow_mul];exact pow_le_pow_left₀ m.le mesh _
  change _≤|b| *_*_
  calc quote R d (tilt n A) j K N per i y=
      b*((a j/a K)^d i*Real.exp (tilt n A*((C).S.scale K-(C).S.scale j))):=by unfold quote b WilsonOriginalMicroscopicGuardedReporters.stretch;ring
    _≤|b| *(_*_):=mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _≤|b| *(z^(A*d i)*Real.exp (Real.log z/((n:ℝ)+1))):=by gcongr
    _=_:=by ring

theorem portfolio (j:Fin n→ℕ)(N per K A:ℕ)(cut:K≤N)(Y:∀i,(C).label (d i))
    (w:∀i,(C).label (d i))(priced:∀i,(F i).coeffSize (w i)≤quote R d (tilt n A) (j i) K N per i (Y i))
    (S:Finset (Fin n)){z:ℝ}(large:1≤z)(mesh:∀i∈S,a (j i)/a K≤z^A):
    (∑q:Selection R d S,‖weight R d N per K w S q‖)≤
      wallet R d (fun i=>variation R d (j i) N per i (Y i)) S*z^(A*height d S+1):=by
  let B(i:Fin n):=variation R d (j i) N per i (Y i)
  let e:=Real.exp (Real.log z/((n:ℝ)+1))
  let M(i:Fin n):=B i*z^(A*d i)*e
  have wage(i:Fin n)(hi:i∈S):(F i).coeffSize (w i)≤M i:=
    (priced i).trans (column R d A (j i) K N per i (Y i) large (mesh i hi))
  apply (WilsonReceivedCanonicalVersePortfolio.priced R d N per K cut w S M wage).trans
  have zp:=zero_lt_one.trans_le large
  have size:(Fintype.card S:ℝ)≤(n:ℝ)+1:=by
    have h:S.card≤n:=by simpa using S.card_le_univ
    rw [Fintype.card_coe];exact_mod_cast (h.trans (Nat.le_succ n))
  have shrink:e^(Fintype.card S)≤z:=by
    dsimp only [e];rw [←Real.exp_nat_mul,←Real.exp_log zp]
    apply Real.exp_le_exp.mpr
    rw [←mul_div_assoc]
    exact (div_le_iff₀ (by positivity:0<(n:ℝ)+1)).mpr (by simpa only [Real.log_exp,mul_comm (Real.log z)] using mul_le_mul_of_nonneg_right size (Real.log_nonneg large))
  let K₀(i:S):=∑c,shoulder R d i c
  have reorder(i:S):K₀ i*M i=(K₀ i*B i)*(z^(A*d i))*e:=by dsimp only [M];ring
  calc wallet R d M S=(∏i:S,K₀ i*M i):=rfl
    _=(∏i:S,K₀ i*B i)*z^(A*height d S)*e^(Fintype.card S):=by
       simp only [reorder,prod_mul_distrib,prod_const,card_univ,prod_pow_eq_pow_sum,←Finset.mul_sum,height]
    _≤(∏i:S,K₀ i*B i)*z^(A*height d S)*z:=by
      apply mul_le_mul_of_nonneg_left shrink
      apply mul_nonneg _ (pow_nonneg zp.le _)
      exact prod_nonneg (fun i _=>mul_nonneg (sum_nonneg fun c _=>nonneg R d i c) (abs_nonneg _))
    _=wallet R d (fun i=>variation R d (j i) N per i (Y i)) S*z^(A*height d S+1):=by
      rw [pow_succ];change _=(∏i:S,K₀ i*B i)*_;ring

end YM.Integration.WilsonOriginalObservedRoseMeshHeight
end
