import YM.Integration.WilsonReflectedMixedSharpAxis
import YM.Integration.WilsonCapturedPrimaryWeakTrialRadial
import YM.Integration.WilsonOriginalFundedPageDecoder

/-! The complete measured row of a named physical source on its already elected weak axis. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryMasterNamedRow
open Function Filter Finset Lattice RG Wilson Source Labels Push.Local Extra.Histories
open Next.Foundations ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02 RG16 RG16.Literal
open WilsonCapturedPrimaryReading WilsonPositionProgramBlockedTrialNodes WilsonCapturedPrimaryWeakTrialRadial
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonOriginalMicroscopicGuardedReporters (Arrived stretch)
open WilsonCapturedPrimaryWeakTrialEngineering (gain)
open WilsonCapturedPrimaryPotential WilsonCapturedPrimaryPaid
open private carry from YM.Integration.WilsonOriginalFundedPageDecoder
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){d j K N per target:ℕ}
local notation "C" => R.family
local notation "F" => (C).labels.level d
local notation "S" => (C).localSection d
local notation "W" => (C).path.rep N per j

/-- The guarded original field on the true conditional and the complete radial invoice use one q. -/
def Filed (d j K N per target:ℕ)(before:j≤K)(live:K≤N)
    (A:(C).label d ≃ₗ[ℂ] (C).label d)(Y:(C).label d):Prop:=
  let frame₀:=(C).labels.level d
  let rep₀:=(C).path.rep N per j
  let e:=fitted R d j N per Y
  let w:=A.symm e
  A w=e ∧ ∃q:Coefficient frame₀ ((C).side j per),
    q.Format 0 (C).params rep₀ ∧ q.remBound 0 rep₀ (safety (C) j) (2*stock (C) j*frame₀.coeffSize e) ∧
    q.density 0 ((C).localSection d) rep₀=WilsonPositionProgramOriginalBlockedTrial.carried R d
      (b:=j) (n:=K-j) (p:=per) (by omega : j+(K-j)≤N) 0 w ∧
    projection frame₀ (C).params rep₀.p.threshold 0 q=e ∧ Invoice R d N per j target e q ∧
    (∀U,reading ((C).localSection d) rep₀ 0 q U=gain R d j (K-j)*
      actualTransport (C) (N:=N) (fun V=>part ((C).localSection d) 0 ((C).path.rep N per K) V w) before U) ∧
    ∀D,d≤D →
      let Yread:=reading ((C).localSection d) rep₀ 0 q
      let err:=gMap (C) N per d j (e-decode R d N per j target D Yread)
      frame₀.coeffSize err≤price R d N per j target D e 0 ∧ ∀a,‖err a‖≤price R d N per j target D e 0

theorem normalized (before:j≤K)(live:K≤N)(w:(C).label d)(q:Coefficient (F) ((C).side j per))
    (held:q.density 0 (S) (W)=WilsonPositionProgramOriginalBlockedTrial.carried R d
      (b:=j) (n:=K-j) (p:=per) (by omega : j+(K-j)≤N) 0 w)(U:Config G ((C).side j per)):
    reading (S) (W) 0 q U=gain R d j (K-j)*actualTransport (C) (N:=N)
      (fun V=>part (S) 0 ((C).path.rep N per K) V w) before U:=by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le before
  have word:=held.trans (carry R d (show (j+n)-j=n by omega) _ live w)
  simp only [Nat.add_sub_cancel_left]
  unfold reading
  rw [word,div_eq_mul_inv,mul_comm]
  exact WilsonCapturedPrimaryWeakTrialEngineering.normalized R d N per j live 0 w U

theorem original (before:j<K)(live:K≤N){η:ℝ}
    (A:(C).label d ≃ₗ[ℂ] (C).label d)(Y:(C).label d)
    (sold:Arrived R d j K N per target before.le live η A (fitted R d j N per Y)):
    Filed R d j K N per target before.le live A Y:=by
  obtain ⟨_,q,form,rem,full,proj,invoice⟩:=sold
  exact ⟨A.apply_symm_apply _,q,form,rem,full,proj,invoice,normalized R before.le live _ q full,
    fun D eligible=>WilsonCapturedPrimaryWeakTrialRadial.original R d N per j target D
      (before.trans_le live) eligible q _ invoice⟩

end YM.Integration.WilsonCapturedPrimaryMasterNamedRow
end
