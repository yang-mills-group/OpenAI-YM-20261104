import YM.Integration.WilsonOriginalObservedRoseFittedPurse
import YM.Integration.WilsonMovingForkRawSeed
import YM.Integration.WilsonReflectedMixedIntrinsicAxis

/-! The optical inverse is intrinsic on its own full measured input. Its fine K quote can use any fixed positive stretch before later phase and Taylor orders. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseMeshPurse
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

def quote (η:ℝ)(j K N per:ℕ)(i:Fin n)(y:(C).label (d i)):ℝ:=
  orbitCost (F i)*(a j/a K)^(d i)*
    (stretch R η j K*((1+WilsonOriginalMicroscopicGuardedPage.wrapCost R (d i) j)*
      Next.Rank.Spindle.paid (C) (d i) j N per y))

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1≤((C).path.levels.budget j).supportExponent){η:ℝ}(hp:0<η):
    ∃L:ℕ,∀N per f K:ℕ,∀fk:f≤K,∀cut:K≤N,∀requested power t:ℕ,∀B:ℝ,
      ∀A:Panel R d N per f K fk cut requested power t B,∀file:Filed R d K,
      A.slot=file.station→A.axis=file.A N per→(∀i,L≤A.slot i)→f<N→
      let w:=votes R d (N:=N) (per:=per) file A.names A.turn
      (∀i,(F i).coeffSize (w i)≤quote R d η (A.slot i) K N per i (A.names i)) ∧
      ∀s:(J).Mode,(∑q:Selection R d s.val,‖weight R d N per K w s.val q‖)≤
        wallet R d (fun i=>quote R d η (A.slot i) K N per i (A.names i)) s.val:=by
  have offers(i:Fin n):=WilsonMovingForkRawSeed.original R simple shop wide (d i) 0 hp
  choose start offered using fun i:Fin n=>eventually_atTop.mp (offers i)
  refine ⟨univ.sup fun i=>max (start i) ((C).ref (d i)),?_⟩
  intro N per f K fk cut requested power t B A file station axes early deep w
  have cash(i:Fin n):(F i).coeffSize (w i)≤quote R d η (A.slot i) K N per i (A.names i):=by
    let j:=A.slot i
    have ready:max (start i) ((C).ref (d i))≤j:=(le_sup (f:=fun p=>max (start p) ((C).ref (d p))) (mem_univ i)).trans (early i)
    have jk:j≤K:=(A.before i).trans fk
    have jN:j<N:=(A.before i).trans_lt deep
    obtain ⟨other,quote₀⟩:=offered i j ((le_max_left ..).trans ready) K N per jk cut jN
    let degree:Fin (d i+1):=⟨d i,Nat.lt_succ_self _⟩
    let Y:=A.names i
    let e:=full R (d i) N per j Y
    have eq:e=fitted R (d i) j N per Y:=page_at R (d i) jN.le Y
    have bought:=quote₀ degree Y
    have same:(other degree).symm e=(A.axis i).symm e:=
      WilsonReflectedMixedIntrinsicAxis.original R ((le_max_right ..).trans ready) jk cut bought.2.1 (A.fixed i).1
    let v:=(A.axis i).symm (fitted R (d i) j N per Y)
    have measured:(F i).coeffSize v≤ stretch R η j K*((1+WilsonOriginalMicroscopicGuardedPage.wrapCost R (d i) j)*
        (Next.Rank.Spindle.paid (C) (d i) j N per Y*(a j)^(d i))):=by
      change (F i).coeffSize ((A.axis i).symm (fitted R (d i) j N per Y))≤_
      rw [←eq,←same]
      exact bought.2.2
    have turned:(F i).coeffSize (Motion.patch (F i) (A.turn i) v)≤
        orbitCost (F i)*(stretch R η j K*((1+WilsonOriginalMicroscopicGuardedPage.wrapCost R (d i) j)*
          (Next.Rank.Spindle.paid (C) (d i) j N per Y*(a j)^(d i)))):=
      (patch_cost (F i) (A.turn i) v).trans (mul_le_mul_of_nonneg_left measured (zero_le_one.trans (orbitCost_one_le _)))
    change (F i).coeffSize (((((a K):ℂ)^(d i))⁻¹) • Motion.patch (F i) (A.turn i)
       (doses R d file.station (N:=N) (per:=per) (file.A N per) A.names i))≤_
    rw [←station,←axes,Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((C).S.a_pos K)]
    calc _≤_:=mul_le_mul_of_nonneg_left turned (inv_nonneg.mpr (pow_nonneg ((C).S.a_pos K).le _))
         _=_:=by unfold quote;rw [div_pow];ring
  exact ⟨cash,fun s=>WilsonReceivedCanonicalVersePortfolio.priced R d N per K cut w s.val _ (fun i _=>cash i)⟩

end YM.Integration.WilsonOriginalObservedRoseMeshPurse
end
