import YM.SignedWilsonExpansion.Fire.Lumber
import YM.Integration.WilsonOriginalMicroscopicGuardedReporters
/-! Direct link at the blocking upper epoch to the literal library Arrived. -/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Fire
open Function Filter Finset Lattice RG Wilson Source Labels Trace.Physical.Germ Trace.Physical.GermGraph Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Quince Quince.PreCost
open Purchases UVClock Schedules PurchVoice Extraction Asymptotics Commission
open Integration WilsonPositionProgramOriginalBlockedTrial
open WilsonOriginalMicroscopicGuardedReporters
open WilsonOriginalNullCorridor
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} (R:Run G)(h:G.Simple){n j k N p d t:ℕ}
local notation "C₀"=> R.family

lemma flowX (j n d N p:ℕ)(f:Config G (R.family.side (j+n) p)→ℂ) : blastCurve C₀ d N p j n f=WilsonOriginalNullCorridor.flow C₀ d N p j n f:=by
    induction n with
    | zero=> rfl
    | succ n ih=> rw [blastCurve,flow,ih]; rfl
lemma frost {A:R.family.label d≃ₗ[ℂ] R.family.label d}(hk:j+n=k)(β:j≤k)(v:k≤N)(p:ℕ) (η:ℝ)
    (θ:∀e,Arrived R d j k N p t β v η A e) : ReceivesQ R.family d N p j n A:=by
    subst k; intro e; obtain ⟨-,q,x,y,z,u,fees⟩:=θ e; have hP: ( C₀|>.path.rep N p j ).p=plank C₀ j:= ( R.makes.wilson.represents N p j ( β.trans v ) ).vac
    refine ⟨q,_,?_,⟨x,y⟩,?_⟩
    · rw [page,←hP,u]
    change value d N p j q=carried R d (b:=j) (n:=j+n-j) (p:=p) (N:=N) _ 0 (A.symm e) at z
    rw [z]; let U(nb:ℕ)(h:j+nb≤N):= carried R d (b:=j) (n:=nb) (p:=p) h 0; have he(nb:ℕ)(h:j+nb≤N)(H:nb=n): U nb h=U n v:=by subst nb; rfl
    erw [show carried R d (b:=j) (n:=j+n-j) (p:=p) (N:=N) _ 0 = carried R d (b:=j) (n:=n) (p:=p) v 0 from he _ _ (by omega)]; rw [signalQ,flowX]; rfl
end YM.SignedWilsonExpansion.Fire
