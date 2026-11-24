import YM.Integration.WilsonReflectedRestartedPair
import YM.Integration.WilsonReflectedOriginalVanes
import YM.Integration.WilsonOriginalMicroscopicGuardedReporters

/-! One finite original reflected panel.  Each public candidate keeps the
same cutoff lift and inverse at its own reporter across every pairing.
The reserved trial words all begin at the chosen K on the N-cutoff vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedFourStations
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open GapsContact GapsContact.Seams GapsContact.Stamps Analysis Table Extraction Bid Spec Ascent Trace
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Next.Rank.Price
open PhysicalNext PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals
open WilsonReflectedOriginalTwoDeposit WilsonReflectedOriginalVanes WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedReporters WilsonOriginalMicroscopicGuardedWallet
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){h:Extraction.Order}{S:Table R.family.book}(F:Final R.family h S)
    (l:Ultrafilter (ℕ×ℕ))
local notation "C₀" => R.family
local notation "A₀" => R.family.path.levels

def reading (d j N per:ℕ)(y:(C₀).label d):(C₀).label d:=
  (((C₀).factory d N per).entries j (((C₀).factory d N per).terminal.symm y)).x

/-- Elect the physical columns before N, the inverse before seeing the
opposite member of a pair, and the sites only after the inverse. The
original guarded-to-uncut posterior refund holds on every mixed choice. -/
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((A₀).budget j).supportExponent)(law:OPE.Therm.Poetry (A₀))
    (d:Fin 3→ℕ)(q:ℕ){η:ℝ}(pos:0<η):
    ∃floor:ℕ,∀(r B:Bool→Fin 3→ℝ)(j m:Bool→Fin 3→ℕ)
      (field:∀a:Fin 3, S.Field (d a))
      (_:∀t a,floor≤j t a)
      (_:∀t a,BookedArm F l (r t a) (j t a) (m t a) (d a) (B t a)),
    ∃Y:Bool→∀a:Fin 3,ℕ×ℕ→(C₀).label (d a),
      (∀t a,Captured R F l (r t a) (B t a) (j t a) (m t a) (d a) (field a) (Y t a)) ∧
      ∀K (before:∀t a,j t a ≤ K) N per (high:K≤N) (_:∀t a,j t a<N),
      ∃A:Bool→∀a:Fin 3,(C₀).label (d a) ≃ₗ[ℂ] (C₀).label (d a),
        (∀t a e,Arrived R (d a) (j t a) K N per q (before t a) high η (A t a) e) ∧
        ∀pick:Fin 3→Bool,
          let e:=fun a=>reading R (d a) (j (pick a) a) N per (Y (pick a) a (N,per))
          let w:=fun a=>(A (pick a) a).symm (e a)
          ∀ (o:Fin 3→Site ((C₀).side K per))(s:Finset (Fin 3))(b:ℕ)(past:b≤K),
            (∫U,‖actualTransport (C₀) (N:=N)
              (WilsonOriginalMicroscopicGuardedTrial.gap R d N per K o w s) past U‖
              ∂scene (C₀).path N per b) ≤ invoice R d K (fun a=>WilsonOriginalMicroscopicGuardedReporters.stretch R η (j (pick a) a) K*
               ((C₀).S.a (j (pick a) a)^(d a)*B (pick a) a*cost F (d a) (r (pick a) a) (field a))) s*
                (A₀).clock.forcedAllowance K:=by
  obtain ⟨b,offer⟩:=WilsonOriginalMicroscopicGuardedReporters.original R d simple shop wide law q pos
  obtain ⟨f,refund⟩:=eventually_atTop.mp (WilsonOriginalMicroscopicGuardedPosterior.paid R d simple law)
  refine ⟨max b f,?_⟩
  intro r B j m field early hit
  choose Y source using fun t a=>enrolled R F l (field a) (hit t a)
  refine ⟨Y,source,?_⟩
  intro K before N per high nonbare
  have appoint (t:Bool):∃A:∀a:Fin 3,(C₀).label (d a) ≃ₗ[ℂ] (C₀).label (d a),
      ∀a e,Arrived R (d a) (j t a) K N per q (before t a) high η (A a) e:=by
    obtain ⟨A,grant,_⟩:=offer (j t) (fun a=>(le_max_left ..).trans (early t a)) K (before t)
      (fun _=>0) N per high (nonbare t)
    exact ⟨A,grant⟩
  choose A grant using appoint
  refine ⟨A,grant,?_⟩
  intro pick e w o s past earlier
  have u:f≤K:=(le_max_right ..).trans ((early false 0).trans (before false 0))
  apply (refund K u N high per o w s past earlier).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  apply WilsonOriginalMicroscopicGuardedWallet.original R d N per K high w
  intro a
  have earned:((C₀).labels.level (d a)).coeffSize (e a) ≤ _ :=
    (source (pick a) a).quota N per (nonbare (pick a) a)
  exact ((grant (pick a) a (e a)).1).trans
    (mul_le_mul_of_nonneg_left earned (by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity))

end YM.Integration.WilsonReflectedFourStations
end
