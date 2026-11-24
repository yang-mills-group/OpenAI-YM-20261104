import YM.Integration.WilsonOriginalObservedRoseMeshHeight
import YM.Integration.WilsonOriginalObservedRoseFittedWeights

/-! The physical radius rescales the entire finite roster before spending its Taylor order. The constant source and every complex core coordinate use the same original scalar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseScaledWallet
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

open WilsonOriginalObservedRoseMeshHeight (tilt variation height)
open WilsonReceivedCanonicalVerseBasis (dose)

def share (n:ℕ)(z:ℝ):ℝ:=Real.exp (Real.log z/((n:ℝ)+1))

private theorem packed (S:Finset (Fin n)){z:ℝ}(large:1≤z):share n z^(Fintype.card S)≤z:=by
  have size:(Fintype.card S:ℝ)≤(n:ℝ)+1:=by
    have h:S.card≤n:=by simpa using S.card_le_univ
    rw [Fintype.card_coe];exact_mod_cast (h.trans (Nat.le_succ n))
  unfold share
  rw [←Real.exp_nat_mul,←Real.exp_log (zero_lt_one.trans_le large)]
  apply Real.exp_le_exp.mpr
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity:0<(n:ℝ)+1)).mpr
  simpa only [Real.log_exp,mul_comm (Real.log z)] using mul_le_mul_of_nonneg_right size (Real.log_nonneg large)

theorem columns (A j K N per:ℕ)(i:Fin n)(y w:(C).label (d i)){r z:ℝ}(rp:0<r)(large:1≤z)
    (age:a j/a K≤z^A)(top:r/a K≤z^A){B:ℝ}
    (paid:(F i).coeffSize w≤quote R d (tilt n A) j K N per i y)
    (liquid:variation R d j N per i y*(a j)^d i≤B):
    r^(d i)*(F i).coeffSize w≤B*z^(A*d i)*share n z:=by
  have mj:0<a j/a K:=div_pos ((C).S.a_pos _ ) ((C).S.a_pos _)
  have time:Real.log (a j/a K)=(C).S.scale K-(C).S.scale j:=by
    rw [Real.log_div ((C).S.a_pos _).ne' ((C).S.a_pos _).ne'];simp only [Schedule.scale,Real.log_inv];ring
  have span:=Real.log_le_log mj age
  rw [time,Real.log_pow] at span
  have ep:0≤tilt n A:=by unfold tilt;positivity
  have clock:Real.exp (tilt n A*((C).S.scale K-(C).S.scale j))≤ share n z:=by
    apply Real.exp_le_exp.mpr
    calc _≤tilt n A*(((A:ℝ)+1)*Real.log z):=mul_le_mul_of_nonneg_left (by linarith [Real.log_nonneg large]) ep
         _=_:=by unfold tilt;field_simp
  let b:=2*orbitCost (F i)*((1+WilsonOriginalMicroscopicGuardedPage.wrapCost R (d i) j)*Next.Rank.Spindle.paid (C) (d i) j N per y)
  have bound:0≤B:=(mul_nonneg (abs_nonneg _) (pow_nonneg ((C).S.a_pos j).le _)).trans liquid
  have physical:(r/a K)^(d i)≤z^(A*d i):=by rw [pow_mul];exact pow_le_pow_left₀ (div_pos rp ((C).S.a_pos K)).le top _
  have aj:0≤(a j)^(d i):=pow_nonneg ((R.family).S.a_pos j).le _
  have radius:0≤(r/a K)^(d i):=pow_nonneg (div_pos rp ((R.family).S.a_pos K)).le _
  calc r^(d i)*(F i).coeffSize w≤r^(d i)*quote R d (tilt n A) j K N per i y:=
         mul_le_mul_of_nonneg_left paid (pow_nonneg rp.le _)
       _=b*((a j)^d i*(r/a K)^d i*Real.exp (tilt n A*((C).S.scale K-(C).S.scale j))):=by
         unfold quote b WilsonOriginalMicroscopicGuardedReporters.stretch;rw [div_pow,div_pow];ring
       _≤|b| *((a j)^d i*(r/a K)^d i*Real.exp (tilt n A*((C).S.scale K-(C).S.scale j))):=
         mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
       _=(variation R d j N per i y*(a j)^d i)*(r/a K)^d i*Real.exp (tilt n A*((C).S.scale K-(C).S.scale j)):=by
         change _=(|b| *_)*_*_;ring
       _≤B*z^(A*d i)*share n z:=by gcongr

theorem original (N per K A:ℕ)(live:K≤N)(w:∀i,(C).label (d i))(S:Finset (Fin n))(B:Fin n→ℝ)
    {r z:ℝ}(rp:0<r)(large:1≤z)(base:∀i,0≤B i)
    (fees:∀i∈S,r^d i*(F i).coeffSize (w i)≤B i*z^(A*d i)*share n z):
    r^height d S*(∑q:Selection R d S,‖weight R d N per K w S q‖)≤
      wallet R d B S*z^(A*height d S+1):=by
  let ρ(i:Fin n):ℂ:=(r:ℂ)^d i
  let u(i:Fin n):=ρ i • w i
  let M(i:Fin n):=B i*z^(A*d i)*share n z
  have cost(i:Fin n)(h:i∈S):(F i).coeffSize (u i)≤M i:=by
    dsimp only [u,ρ];rw [Size.smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos rp];exact fees i h
  have scales(q:Selection R d S):weight R d N per K u S q=(r:ℂ)^(height d S)*weight R d N per K w S q:=by
    unfold WilsonReceivedCanonicalVersePortfolio.weight
    simp_rw [u,WilsonOriginalObservedRoseFittedWeights.slot R d]
    rw [prod_mul_distrib];dsimp only [ρ];rw [prod_pow_eq_pow_sum];rfl
  have share₀:0≤ share n z:=(Real.exp_pos _).le
  let cost₀(i:S):=∑c,shoulder R d i c
  have reorder(i:S):cost₀ i*M i=(cost₀ i*B i)*z^(A*d i)*share n z:=by dsimp only [M];ring
  have finish:wallet R d M S≤wallet R d B S*z^(A*height d S+1):=calc
    _=(∏i:S,cost₀ i*M i):=rfl
    _=(∏i:S,cost₀ i*B i)*z^(A*height d S)*share n z^(Fintype.card S):=by
       simp only [reorder,prod_mul_distrib,prod_const,card_univ,prod_pow_eq_pow_sum,←Finset.mul_sum,WilsonOriginalObservedRoseMeshHeight.height]
    _≤(∏i:S,cost₀ i*B i)*z^(A*height d S)*z:=by
      apply mul_le_mul_of_nonneg_left (packed S large)
      exact mul_nonneg (prod_nonneg fun i _=>mul_nonneg (sum_nonneg fun c _=>nonneg R d i c) (base i)) (pow_nonneg (zero_le_one.trans large) _)
    _=wallet R d B S*z^(A*height d S+1):=by rw [pow_succ];change _=(∏i:S,cost₀ i*B i)*_;ring
  have assign:∑q:Selection R d S,‖weight R d N per K u S q‖=r^height d S*∑q:Selection R d S,‖weight R d N per K w S q‖:=by
    simp_rw [scales,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos rp];rw [Finset.mul_sum]
  rw [←assign]
  exact (WilsonReceivedCanonicalVersePortfolio.priced R d N per K live u S M cost).trans finish

end YM.Integration.WilsonOriginalObservedRoseScaledWallet
end
