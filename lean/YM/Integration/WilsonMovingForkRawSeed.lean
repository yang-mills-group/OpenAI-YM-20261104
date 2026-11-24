import YM.Integration.WilsonOriginalMicroscopicGuardedReporters
import YM.Integration.WilsonOriginalMicroscopicGuardedPage
import YM.Integration.WilsonOriginalTwoFlatPublicFare

/-! One true measured inverse for each retained grade at the common aligned reporter.
The public source vectors, occupied marked subsets and their physical sites are chosen later. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMovingForkRawSeed
open Next.Rank
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Trace.Physical
open Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicGuardedReporters WilsonOriginalMicroscopicGuardedPage
open WilsonPositionProgramBlockedPublicExperiment WilsonPositionProgramBlockedTrialAddBack
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "Lv" => R.family.path.levels

def column {j N per d:ℕ}(A:(C).label d ≃ₗ[ℂ] (C).label d)(y:(C).label d):(C).label d:=
  A.symm (full R d N per j y)

def print {ι:Type}[DecidableEq ι]{j K N per D:ℕ}(d:ι→Fin (D+1))
    (A:∀a:Fin (D+1),(C).label a ≃ₗ[ℂ] (C).label a)(Y:∀i,(C).label (d i))
    (o:ι→Site ((C).side K per))(s:Finset ι)(U:Config G ((C).side K per)):ℂ:=
  ∏i∈s,uncut R (d i) N per K (o i) (column R (j:=j) (N:=N) (per:=per) (A (d i)) (Y i)) U

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((Lv).budget j).supportExponent)(D target:ℕ){η:ℝ}(ep:0<η):
    ∀ᶠ j:ℕ in atTop,∀ K N per,∀ jk:j ≤ K,∀kn:K ≤ N,j<N →
      ∃ A:∀d:Fin (D+1),(C).label d ≃ₗ[ℂ] (C).label d,
      ∀(d:Fin (D+1))(y:(C).label d),
        let e:=full R d N per j y
        let w:=column R (j:=j) (N:=N) (per:=per) (A d) y
        A d w=e ∧ Arrived R d j K N per target jk kn η (A d) e ∧
        ((C).labels.level d).coeffSize w ≤
          stretch R η j K*((1+wrapCost R d j)*(Spindle.paid C d j N per y*(C).S.a j^d.val)):=by
  have shots(d:Fin (D+1)):=WilsonPositionProgramBlockedTrialNodes.original R d simple shop wide target ep
  have ready(d:Fin (D+1)):∀ᶠj:ℕ in atTop,R.t d ≤ j ∧ (C).ref d ≤ j:=
    (eventually_ge_atTop _).and (eventually_ge_atTop _)
  filter_upwards [eventually_all.mpr shots,eventually_all.mpr ready] with j offer late
  intro K N per jk kn seen
  have age:j+(K-j)=K:=by omega
  have solved(d:Fin (D+1)):∃A:(C).label d ≃ₗ[ℂ] (C).label d,
      ∀e,Arrived R d j K N per target jk kn η A e:=by
    obtain ⟨A,granted⟩:=offer d N per (K-j) (by omega) seen
    refine ⟨A,fun e=>?_⟩
    obtain ⟨price,raw⟩:=granted e
    exact ⟨by simpa only [stretch,age] using price,raw⟩
  choose A receipt using solved
  refine ⟨A,?_⟩
  intro d y
  have wage:=WilsonOriginalMicroscopicGuardedPage.wage R d (p:=per) (late d).1 (late d).2 seen.le (wide j) y
  have paid:=receipt d (full R d N per j y)
  dsimp only [column]
  refine ⟨(A d).apply_symm_apply _,paid,paid.1.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold stretch;positivity)
  rw [WilsonMatrixTicketLanesQuota.quota]
  exact wage.2

end YM.Integration.WilsonMovingForkRawSeed
