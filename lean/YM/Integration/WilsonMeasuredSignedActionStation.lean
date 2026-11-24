import YM.Integration.WilsonMeasuredSignedActionBooked
import YM.Integration.WilsonPhysicalChiralNonfreeStationMoney
import YM.Integration.WilsonPhysicalChiralNonfreeStationSize
import YM.Integration.WilsonCapturedPrimaryMasterNamedRow

/-! The filed K-source on its N-inherited vacuum has the signed station
reading of the voted action. The winding coefficient is measured at this
date, before the period and then the small-distance limit. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionStation
open Function Filter Set Finset Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Source Labels
open Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open PhysicalNext.Repeat.Legato Further.CorrectedLift RG05Readout.Address Next.Rank.Atlas
open Next.Rank.Price Next.Rank.Station WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMeasuredPublicEntranceGridDebit WilsonMaxwellThermometerMaximalHead
open WilsonMaxwellThermometerStationHeads WilsonPhysicalChiralNonfreeStationMoney
open WilsonOriginalTwoFlatPublicBooks WilsonOriginalMicroscopicGuardedReporters
open scoped Topology BigOperators Classical
open private onStation from YM.Integration.WilsonPhysicalChiralNonfreeStationSize
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
local notation "C" => R.family
local notation "road" => (C).path.levels

theorem original (simple:G.Simple):∀ᶠ k:ℕ in atTop,∀{D T:ℕ}{r:ℝ}
    (B:Book F (l:=l) H Z D T r) (i:Fin (D+1)) (v:S.Field i),
    B.W.k=k → ∀N per K target:ℕ,∀(old:k<K)(top:K≤N),
    R.t i≤k → (C).ref i≤k → 1≤((C).path.levels.budget k).supportExponent →
    ∀(A:(C).label i ≃ₗ[ℂ] (C).label i){η:ℝ},
    let U:=B.V i
    let y:=((B.rows i).arm true v).source (N,per)
    let e:=fitted R i k N per y
    let w:=A.symm e
    let p:=ladder C i (U.symm v)
    let χ:=(shrink C k N per)^(i.val/2)/(Station.mag road B.W.b k)^i.val
    let a:=(((C).S.a k:ℂ)^i.val)⁻¹
    Arrived R i k K N per target old.le top η A e →
      WilsonCapturedPrimaryMasterNamedRow.Filed R i k K N per target old.le top A y ∧
      error ((C).labels.level i) χ (a • A w) p ≤
        (fee R k+|levy R i N per k|)/(1-fee R k)*((C).labels.level i).coeffSize p:=by
  filter_upwards [clock R simple] with k ready
  intro D T r B i v site N per K target old top early ref width A η U y e w p χ a reached
  refine ⟨WilsonCapturedPrimaryMasterNamedRow.original R old top A y reached,?_⟩
  subst k
  let slot:Fin (B.k+1):=⟨i.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.isLt).trans B.fits)⟩
  have current:B.W.k<N:=old.trans_le top
  have θ:=ready.2.2 N per current.le
  have small:shrink C B.W.k N per≤1:=θ.2.trans ((div_le_one
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ready.2.1)).mpr ready.2.1)
  have mag:1≤Station.mag road B.W.b B.W.k:=
    Real.one_le_rpow ((by norm_num:(1:ℝ)≤2).trans ready.2.1)
      (le_of_lt ((by norm_num:(0:ℝ)<5).trans B.checked.high.1))
  have pos:0≤χ:=div_nonneg (pow_nonneg θ.1.le _) (pow_nonneg (zero_le_one.trans mag) _)
  have plot:y=B.W.wheel.atCut (N,per) slot (U.symm v):=(B.rows i).weak v _
  have bound:=stationed R.makes B.W B.checked slot (U.symm v) N per current mag small ready.1
  have size:=onStation R.makes B.W B.checked slot (U.symm v) N per current mag small ready.1
  have heads:error ((C).labels.level i) χ (awake C i B.W.k N per y) p≤
    fee R B.W.k/(1-fee R B.W.k)*((C).labels.level i).coeffSize p:=by rw [plot];exact bound
  have cost:χ*((C).labels.level i).coeffSize (awake C i B.W.k N per y)≤
    ((C).labels.level i).coeffSize p/(1-fee R B.W.k):=by rw [plot];exact size
  have minus:=WilsonPhysicalChiralNonfreeStationVote.filed R i N per B.W.k early ref current.le width y A χ p
  dsimp only at minus
  rw [WilsonPhysicalChiralNonfreeStationMoney.same R i N per B.W.k y χ pos] at minus
  have levyBound:=mul_le_mul_of_nonneg_left cost (abs_nonneg (levy R i N per B.W.k))
  apply minus.trans
  apply (add_le_add heads ((mul_le_mul_of_nonneg_right (le_abs_self _)
    (mul_nonneg pos (Work.G08.size_nonneg _ _))).trans levyBound)).trans
  apply le_of_eq
  ring

end YM.Integration.WilsonMeasuredSignedActionStation
