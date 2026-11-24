import YM.Integration.WilsonOriginalMicroscopicUpperFlatHalos
import YM.Integration.WilsonOriginalFlatHaloRate
import YM.Integration.WilsonOriginalMicroscopicGuardedWallet

/-! A fixed flat Wilson receiver pays guard removal on each occupied face
of the three true original upper inputs, even at the microscopic endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedFlat
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ)
def peak (K:ℕ)(M:Fin 3→ℝ)(s:Finset (Fin 3)):ℝ:=2*∏a∈s,loss R (d a) K*M a
def count (s:Finset (Fin 3)):ℕ:=∑a∈s,(R.family.localSection (d a)).stencil.card

theorem bound {N p K:ℕ}(live:K≤N)(o:Fin 3→Site (R.family.side K p))
    (v:∀a:Fin 3,R.family.label (d a))(M:Fin 3→ℝ)
    (earned:∀a,(R.family.labels.level (d a)).coeffSize (v a)≤M a)(s:Finset (Fin 3)):
    ∀U,‖gap R d N p K o v s U‖≤peak R d K M s:=by
  intro U
  apply ((occupied R d N p K o v s).2.1 U).trans (mul_le_mul_of_nonneg_left _ (by norm_num))
  apply Finset.prod_le_prod
  · exact fun a _=>add_nonneg (norm_nonneg _) (mul_nonneg (zero_le_one.trans (BasisCost.price_pos _)) (BasisCost.coeff_nonneg _))
  · exact fun a _=>(one R d N p K live v a).trans (mul_le_mul_of_nonneg_left (earned a) (nonneg R _ _))

variable {N per m k K:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (live:K≤N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m≤u)(start:u ≤ K)
   (fixed:WilsonSingleHardRadius.first R simple≤u)
   (capture:WilsonCenteredCaptureClock.first R simple ≤ K)
   (o:Fin 3→Site (R.family.side K per))(v:∀a:Fin 3,R.family.label (d a))(M:Fin 3→ℝ)
   (earned:∀a,(R.family.labels.level (d a)).coeffSize (v a)≤M a)(s:Finset (Fin 3))
local notation "X" => Config G (R.family.side K per)
local notation "Y" => gap R d N per K o v s
local notation "S₀" => footprint R d per K o s
local notation "K₀" => R.alloy.B.a.budget K
local notation "B" => R.alloy.B.a.clock.hatBeta K
local notation "μ" => R.alloy.B.a.clock.forcedAllowance K

include course top floor start fixed capture live way ticket earned in
theorem original {i:ℕ}(reach:u ≤ i)(before:i+1 ≤ K):
    ‖actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans before) 1‖ ≤
      peak R d K M s*((count R d s:ℝ)*(4*hitWidth (K₀)*Real.exp ((K₀).supportExponent+2)*B*μ)):=by
  have g:=bound R d live o v M earned s
  have pos:0≤peak R d K M s:=(norm_nonneg (Y 1)).trans (g 1)
  have truep:=(course.1.walk K (floor.trans start) live).truep.point
  have param:(Ψ K).p=(R.family.path.rep N per K).p:=truep.trans (R.makes.wilson.represents N per K live).vac.symm
  obtain ⟨borel,_,away,_⟩:=occupied R d N per K o v s
  have clear (U:X)(ok:∀a∈S₀,Healthy (Ψ K).p.threshold (halo (Ψ K).p.B {a}) U):‖Y U‖≤0:=by
    apply le_of_eq
    rw [away U]
    · exact norm_zero
    · rintro ⟨a,seat,hot⟩
      have H:=ok a seat
      rw [param] at H
      exact Finset.disjoint_left.mp H (halo_subset _ _ (Finset.mem_singleton_self a)) hot
  have sold:=WilsonOriginalMicroscopicUpperFlatHalos.original R π Γ Ψ course live top
    (R.family.localSection 0) R.family.params simple way D Q ticket floor start fixed capture
    S₀ id Y borel (le_refl 0) pos g clear reach before
  rw [zero_add,truep] at sold
  apply sold.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right _ _) pos)
  · exact_mod_cast (show (S₀).card≤count R d s from Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _=>Finset.card_image_le))
  · have hB:0<B:=zero_lt_one.trans (R.alloy.B.a.fits.delayed K)
    have hμ:0<μ:=Real.exp_pos _
    unfold hitWidth
    positivity

include course top floor start fixed capture live way ticket earned in
theorem power (q:ℕ){ε:ℝ}(ep:0<ε)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple q ep)).choose ≤ K)
    {i:ℕ}(reach:u ≤ i)(before:i+1 ≤ K):
    ‖actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans before) 1‖ ≤
      peak R d K M s*((count R d s:ℝ)*((4*Real.exp ((K₀).supportExponent+2))*(ε/B^q))):=by
  have cash:=original R d π Γ Ψ course live top simple way D Q ticket floor start fixed capture o v M earned s reach before
  have pos:0≤peak R d K M s:=(norm_nonneg _).trans (bound R d live o v M earned s 1)
  obtain ⟨restricted,rare⟩:=(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple q ep)).choose_spec K late
  have good:0≤B:=zero_le_one.trans (R.alloy.B.a.fits.delayed K).le
  apply cash.trans
  apply mul_le_mul_of_nonneg_left _ pos
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _=4*Real.exp ((K₀).supportExponent+2)*(B*(hitWidth (K₀)*μ)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left restricted good).trans rare) (by positivity)

end YM.Integration.WilsonOriginalMicroscopicGuardedFlat
end
