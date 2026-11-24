import YM.Integration.WilsonOriginalMicroscopicGuardedWallet
import YM.Integration.WilsonPositionProgramBlockedTrialNodes

/-! Three independent canonical inverse reporters land at their own physical
dates. Their single original cutoff submits all three guarded sources at K.
The invoices for every face at that date depend on the submitted normalized
coordinate bounds and the paid reporter dates before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedReporters
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals Next.Foundations
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedPosterior WilsonOriginalMicroscopicGuardedWallet
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "H" => R.family.path
local notation "F" d:max => R.family.labels.level d
local notation "κ" => R.family.path.levels.clock.forcedAllowance
def stretch (η:ℝ)(j K:ℕ):ℝ:=2*Real.exp (η*((C).S.scale K-(C).S.scale j))

def Arrived (d j K N p target:ℕ)(before:j ≤ K)(high:K ≤ N)(η:ℝ)
    (A:(C).label d ≃ₗ[ℂ] (C).label d)(e:(C).label d):Prop:=
  let w:=A.symm e
  let W:=(H).rep N p j
  let live:j+(K-j) ≤ N:=by omega
  (F d).coeffSize w ≤ stretch R η j K*(F d).coeffSize e ∧
  ∃q:Coefficient (F d) ((C).side j p),q.Format 0 (C).params W ∧
    q.remBound 0 W (safety (C) j) (2*stock (C) j*(F d).coeffSize e) ∧
    q.density 0 ((C).localSection d) W=WilsonPositionProgramOriginalBlockedTrial.carried R d (b:=j) (n:=K-j) (p:=p) live 0 w ∧
    projection (F d) (C).params W.p.threshold 0 q=e ∧ WilsonPositionProgramBlockedTrialNodes.Invoice R d N p j target e q

theorem original (d:Fin 3→ℕ)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((H).levels.budget j).supportExponent)(quote:Poetry (H).levels)(target:ℕ){η:ℝ}(ep:0 < η):
    ∃L:ℕ,∀(j:Fin 3→ℕ), (∀a,L ≤ j a)→∀ K (before:∀a,j a ≤ K)
      (M:Fin 3→ℝ) N p (high:K ≤ N), (∀a,j a < N)→
    ∃ A:∀a:Fin 3,(C).label (d a) ≃ₗ[ℂ] (C).label (d a),
      (∀a e,Arrived R (d a) (j a) K N p target (before a) high η (A a) e) ∧
      ∀e:∀a:Fin 3,(C).label (d a), (∀a,(F (d a)).coeffSize (e a) ≤ M a)→
      let v:=fun a=>(A a).symm (e a)
      ∀(o:Fin 3→Site ((C).side K p))(s:Finset (Fin 3)) u (prior:u ≤ K),
        (∫U,‖actualTransport (C) (N:=N) (gap R d N p K o v s) prior U‖ ∂scene (H) N p u) ≤
        invoice R d K (fun a=>stretch R η (j a) K*M a) s*(κ) K:=by
  choose gates checks using fun a:Fin 3=>Filter.eventually_atTop.mp
    (WilsonPositionProgramBlockedTrialNodes.original R (d a) simple shop wide target ep)
  obtain ⟨T,pay⟩:=Filter.eventually_atTop.mp (WilsonOriginalMicroscopicGuardedPosterior.paid R d simple quote)
  refine ⟨max T (univ.sup gates),?_⟩
  intro j early K before M N p high seen
  have Kpaid:T ≤ K:=(le_max_left ..).trans ((early 0).trans (before 0))
  have solved (a:Fin 3):∃ A:(C).label (d a) ≃ₗ[ℂ] (C).label (d a),
      ∀e,Arrived R (d a) (j a) K N p target (before a) high η A e:=by
    have gate:gates a ≤ j a:=(Finset.le_sup (f:=gates) (mem_univ a)).trans ((le_max_right ..).trans (early a))
    have ja:=before a
    have amount:j a+(K-j a)=K:=by omega
    obtain ⟨A,issue⟩:=checks a (j a) gate N p (K-j a) (by omega) (seen a)
    refine ⟨A,fun e=>?_⟩
    obtain ⟨price,receipt⟩:=issue e
    exact ⟨by simpa only [stretch,amount] using price,receipt⟩
  choose A sale using solved
  refine ⟨A,sale,?_⟩
  intro e limit v o s u prior
  have purchased:=pay K Kpaid N high p o v s u prior
  apply purchased.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  apply WilsonOriginalMicroscopicGuardedWallet.original R d N p K high v
  intro a
  exact ((sale a (e a)).1).trans (mul_le_mul_of_nonneg_left (limit a) (by unfold stretch;positivity))

end YM.Integration.WilsonOriginalMicroscopicGuardedReporters
end
