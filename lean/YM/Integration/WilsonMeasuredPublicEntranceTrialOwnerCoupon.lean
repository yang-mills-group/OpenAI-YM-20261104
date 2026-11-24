import YM.Integration.WilsonMeasuredPublicEntranceTrialPeerBoard
import YM.Integration.WilsonMeasuredPublicEntranceCropRate
import YM.Integration.WilsonMeasuredPublicEntranceOwnerOptical
import YM.Integration.WilsonMeasuredPublicEntranceReserveWallet
/-! A real guarded owner tested on its actual activity table by a
finite mixture of both original sorts of ordinary peers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTrialOwnerCoupon
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open Source Labels WilsonOriginalAlternativeHearing WilsonMeasuredCoefficientTransport
open Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

open Ac Push.AbsoluteSums PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFieldRange
private theorem narrow {T I V:Type}[DecidableEq V]{G:Gauge}{n:Side}{P:BudgetPoint}{o:V → Site n}{R:Marker.Census V}{w:V → ℝ}{lower upper fee:ℝ}{B:ℕ} (L:Lamps T I G P o R) (positive:∀v,0<w v) (order:lower ≤ upper)
    (paid:L.Paid w B upper fee):L.Paid w B lower fee:=by
  obtain ⟨f,fp,read,bill⟩:=paid.budget
  have toll (mode:R.Mode):0 ≤ Poly.toll w mode:=Finset.prod_nonneg fun v _=>(positive v).le
  refine ⟨f,fp,read,fun x=>budget_mono (bill x) ?_ ?_⟩
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (toll _) (fp i)) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i
    split
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (toll _) (fp i))
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right order (Nat.cast_nonneg _))
    · exact le_rfl

include simple in
theorem original (n d a p:ℕ) (np:0<n) (load:∀s:marks.Mode,s.val.card ≤ n)
    (C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀ᶠ k:ℕ in atTop,∀ (N per m school b:ℕ),let f:=k+1
    ∀(_cut:f ≤ N)(bt:b<f),start ≤ b →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per school Ψ → TicketP R.alloy R.kit D Q →
    ∀(deg:V→ℕ)(o:V→Site (R.family.side f per))(q:∀i,Coefficient (R.family.labels.level (deg i)) (R.family.side f per))
      (w B:V→ℝ)(X I:Type) [Countable I] (Y:Lamps X I G (Ψ f).p o marks)(x:X)(trial:Finset V)(A U Vmax:ℝ),
    let P:=R.family.path.rep N per f
    let clip:=WilsonMeasuredPublicEntranceCropRate.depth n p (H f) U
    let C₀:=WilsonMeasuredPublicEntranceTrialPeerBoard.price (N:=N) R deg o (Ψ f) q trial w (fun _=>clip) B A
    let μ:=fun i=>if i∈trial then A/w i else cost G (deg i) P.p.threshold*(R.family.labels.level (deg i)).coeffSize (q i).x+B i
    let raw:=WilsonMeasuredPublicEntranceTrialPeerBoard.field (N:=N) R marks deg o (Ψ f) q Y x trial
    (∀i,0<w i) → (∀i,0 ≤ B i) → (∀i,R.family.ref (deg i) ≤ f) →
    (∀i,(q i).Format (o i) R.family.params P) → (∀i,(q i).remBound (o i) P (κ f) (B i)) →
    1 ≤  P.p.supportExponent → (Ψ f).p=P.p → Y.Paid w (Ψ f).p.B ((Ψ f).p.supportExponent+2) A →
    0 ≤ U → 0 ≤ Vmax → (∀i,μ i ≤ Real.exp U) → (∀i,B i ≤ Real.exp U) →
    (∀i,(w i)⁻¹ ≤ Real.exp Vmax) → C₀ ≤ Real.exp Vmax →
    ((f-b+Nat.ceil (2*Vmax):ℕ):ℝ) ≤ C*(1+Real.log (H f))^d →
    ∀(owner:V)(s:marks.Mode),owner∈s.val →
    ∀(degree:ℕ)(h:Coefficient (R.family.labels.level degree) (R.family.side f per)) {M amount:ℝ},
    h.Format (o owner) R.family.params (Ψ f) → h.remBound (o owner) (Ψ f) (κ f) M →
    h.x=0 → h.regular=0 → (∀Z,‖h.density (o owner) (R.family.localSection degree) (Ψ f) Z/((Ψ f).eval Z:ℂ)‖ ≤ amount) →
    2*(w owner*M) ≤ Real.exp Vmax → amount ≤ Real.exp U →
    ∀(u i:ℕ),(mu:m ≤ u) → (ui:u ≤ i) → (ib:i ≤ b) → WilsonSingleHardRadius.first R simple ≤ u →
    ∀(Z:Support (R.family.side b per))(center:Site (R.family.side b per)),center∈Z →
    (∀v∈s.val,sites R o bt.le v∈Z) →
    let realW:=QuadraticLocal.Stoop.radius w (WilsonMeasuredPublicEntranceOwnerWallet.divisor w owner C₀ M)
    let fee:=Poly.toll (wallet R realW bt.le) s
    let roof:=(shards marks s).card+4*(fee+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta b*(κ b)
    ‖reading R (N:=N) (fun Z=>account h (Ψ f) Z*∏j∈s.val.erase owner,raw j Z) i (ib.trans bt.le)‖ ≤ 
      ((H f)^p)⁻¹+(e*(regulatorRun R.family N per f)^p)*roof:=by
  classical
  obtain ⟨start,issued⟩:=WilsonMeasuredPublicEntranceOwnerOptical.original R simple marks n d a p np load C e cp ep
  have realh:∀ᶠ j:ℕ in atTop,1 ≤ H (j+1):=((RG01.Physical.hats simple R.family.path.levels).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 1
  refine ⟨start,?_⟩
  filter_upwards [issued,realh] with k earn hH N per m school b f cut bt late way D Q π Γ Ψ course ticket deg o q w B X I ci Y x trial A U Vmax P clip C₀ μ raw wp bp refs fit remn room represent yp up big source partialFee budget fare time owner s present degree h M amount hf hr hz hreg ceiling full hardCap u i mu ui ib eligible Z center home houses realW fee roof
  have running:=course.1.walk f (((mu.trans ui).trans ib).trans bt.le) cut
  obtain ⟨J,ct,L,spending,seen,_,tails⟩:=WilsonMeasuredPublicEntranceTrialPeerBoard.original R marks cut deg refs o
    (Ψ f) represent running.view q Y x trial w wp (fun _=>clip) fit remn room yp
  letI:Countable J:=ct
  have low:=narrow L wp (by linarith : (Ψ f).p.supportExponent ≤ (Ψ f).p.supportExponent+2) spending
  have sale:=earn N per m school b (Nat.ceil (2*Vmax)) cut bt late time way D Q π Γ Ψ course ticket
    Unit J o L owner degree h hf hr w wp low () s u i mu ui ib eligible Z center home houses
  have gain:=WilsonMeasuredPublicEntranceReserveWallet.funded (marks:=marks) (H f) hH a n load w wp owner C₀ M Vmax big budget fare full s
  have heard:=sale.2 gain
  let clipped:=WilsonMeasuredPublicEntranceTrialPeerBoard.clipped (N:=N) R marks deg o (Ψ f) q Y x trial (fun _=>clip)
  have exactCofactor :
      (fun Z=>account h (Ψ f) Z*WilsonMeasuredCompanionFace.peers L owner s () Z)=
      (fun Z=>account h (Ψ f) Z*∏j∈s.val.erase owner,clipped j Z):=by
    funext Z; rw [seen owner s present]
  have paid :‖reading R (N:=N) (fun Z=>account h (Ψ f) Z*∏j∈s.val.erase owner,clipped j Z) i (ib.trans bt.le)‖ ≤ 
      e*(regulatorRun R.family N per f)^p*roof:=by
    rw [exactCofactor] at heard
    simpa only [WilsonOriginalAlternativeHearing.held,reading,Complex.real_smul,Complex.ofReal_inv] using heard
  let δ(j:V):ℝ:=if j∈trial then 0 else Real.exp (-P.p.supportExponent*clip)*B j
  have d0(j:V):0 ≤ δ j:=by
    dsimp [δ]
    split
    · exact le_rfl
    · exact mul_nonneg (Real.exp_nonneg _) (bp j)
  have a0(j:V):0 ≤ μ j:=by
    have regular:=WilsonMeasuredPublicEntrancePeerTests.trial R (Ψ f) o j Y x w wp (by rw [represent];linarith) yp
    dsimp [μ];split
    · exact (norm_nonneg _).trans (regular.2 1)
    · exact (norm_nonneg _).trans (WilsonThermometerUnitFilingFieldRange.point R (deg j) P (q j) (o j) (remn j) 1)
  have dur(j:V):δ j ≤ Real.exp (-(clip:ℝ))*Real.exp U:=by
    dsimp [δ];split
    · positivity
    · apply mul_le_mul _ (partialFee j) (bp j) (Real.exp_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right room (Nat.cast_nonneg clip : 0 ≤ (clip:ℝ))]
  have length:((s.val.erase owner).toList).length ≤ n:=by
    rw [Finset.length_toList]
    exact (Finset.card_le_card (Finset.erase_subset ..)).trans (load s)
  have small:=WilsonMeasuredPublicEntranceCropRate.original n p (H f) U hH up clip (le_refl _)
    μ δ amount a0 d0 source dur hardCap _ length
  have bridge:=(tails owner s degree h running.truep.valid hf hr hz hreg ceiling i (ib.trans bt.le)).trans small
  exact (norm_le_norm_sub_add _ _).trans (add_le_add bridge paid)

end YM.Integration.WilsonMeasuredPublicEntranceTrialOwnerCoupon
end
