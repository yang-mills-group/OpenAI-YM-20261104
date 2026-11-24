import YM.Integration.FVA1Physical.Sources.Round2.StaticBarePrice
import YM.Integration.FVA1Physical.Wilson.VolumeGeometry

/-! Pay the period-uniform normalized marked Wilson stationary-phase
remainder at the actual top coupling of every stage in one common run.
The stage threshold can be combined with any other obtainable invoice. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Lattice RG Wilson Precision Tree Marker Comparison.RG02
open FVA2.CityHistory FormalOPE.RG10.InversionTop RGComparison.Core16
open PhysicalNext.Repeat.Legato PertExtension.Series.Tested Pert.Asymptotics
open YM.Integration.FVA1Physical.Wilson YM.Qlocal.Schedule
open scoped Classical BigOperators Topology
variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I] (R : Census I)

private theorem buy_error {δ : ℝ} (hd : 0<δ) (C η : ℝ) (he : 0<η) (r : ℕ) :
    ∃ b, ∀ β : ℝ, b ≤ β → let g:=(Real.sqrt β)⁻¹
      0<g ∧ g ≤ δ ∧ C*g^(r+1) ≤ g^((r:ℝ)+1-η) := by
  apply eventually_atTop.1
  filter_upwards [eventually_ge_atTop (δ⁻¹^2),eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (show 0<η/2 by positivity)).eventually_ge_atTop C] with β ht hβ hC g
  have hg : 0<g:=inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hs : δ⁻¹≤Real.sqrt β:=by
    simpa only [Real.sqrt_sq (inv_nonneg.mpr hd.le)] using Real.sqrt_le_sqrt ht
  refine ⟨hg,?_,?_⟩
  · simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hd) hs
  · have eqn : β^(η/2) = g^(-η) := by
      change β^(η/2) = ((Real.sqrt β)⁻¹)^(-η)
      rw [Real.sqrt_eq_rpow,← Real.rpow_neg hβ.le,← Real.rpow_mul hβ.le]
      congr 1;ring
    calc C*g^(r+1) ≤ g^(-η)*g^(r+1):= mul_le_mul_of_nonneg_right (hC.trans_eq eqn) (pow_nonneg hg.le _)
         _ = g^((r:ℝ)+1-η):=by rw [←Real.rpow_natCast g (r+1),←Real.rpow_add hg];congr 1;push_cast;ring

/-- The full, separately normalized bare conditional versus its independently generated
joint Wilson coefficients, with the manuscript's arbitrary small loss of order.
The coupling in this statement is the actual bare coupling selected by the run. -/
def PaidBare (A : Run G) (d r : ℕ) (Q η : ℝ) : Prop :=
  ∀ (m p : ℕ), let S:=A.family.path.levels.clock.op m p
  Bid.Larger (G:=G) S → ∀ (a : I → CoverLabel G d) (s : R.Mode)
    (y : I → Site (A.family.side (m+1) p)) (F : Forest S.ratio) (t : S.Choices)
    (u : Pins G (A.family.side m p)) (L : Bulk.Chain A.family.path), (∀ e, ‖u e‖ ≤ Q) →
    let g:=regulatorRun A.family (m+1) p (m+1)
    let x:=axesP G _ u; let U:=placeLabels (C:=A.family) a y
    let v:=fun k=>(MSMatch.SourceTop.datum R m p U F t x).ordinaryCoefficient L r k s
    ‖(MSMatch.SourceTop.torusVacuum (C:=A.family) m p x g)⁻¹ •
      MSMatch.SourceTop.torusFull m p U x s.val g - peval v r g‖ ≤ g^((r:ℝ)+1-η)

theorem scheduled_bare_price (hG : G.Simple) (d r : ℕ) (Q η : ℝ) (hQ : 0<Q) (hη : 0<η) :
    ∃ f : StageThreshold, Obtainable (selectedThreshold (G:=G) f) ∧
      ∀ A : Run G, selectedThreshold f A.metals A.rolls A.alloy A.kit → PaidBare R A d r Q η := by
  choose δ C hδ _ offer using static_bare_price (G:=G) R d r Q hQ
  choose b secure using fun P K=> buy_error (hδ P K) (C P K) η hη r
  let f:StageThreshold:=fun _ _ P K=>2*b P K
  refine ⟨f,selectedThreshold_obtainable f,?_⟩
  intro A invoice m p S room a s y F t u L hu g x U v
  let θ:=A.family.path.levels.clock.hatBeta
  have entry : 2*b S.patch S.kernel ≤ θ m:=invoice m p
  have mono : θ m ≤ θ (m+1):=WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos hG).le (Nat.le_succ m)
  let β:=A.family.path.β (m+1) p (m+1)
  have band : θ (m+1)/2 ≤ β:=(A.makes.wilson.represents (m+1) p (m+1) le_rfl).band.1
  obtain ⟨positive,aperture,pay⟩:=secure S.patch S.kernel β (by linarith only [entry,mono,band])
  exact (offer S.patch S.kernel a s A m p rfl rfl y F t u L room hu g positive aperture).trans pay

theorem run_with_bare_prices {H : Goal G} (hG : G.Simple) (working : Obtainable H)
    (penalty Q η : ℝ) (hp : 0<penalty) (hQ : 0<Q) (hη : 0<η) (d r : ℕ) :
    ∃ A : Run G, A.family.path.levels.clock.kernel.penalty=penalty ∧ H A.metals A.rolls A.alloy A.kit ∧
      PaidBare R A d r Q η := by
  obtain ⟨f,paid,act⟩:=scheduled_bare_price R hG d r Q η hQ hη
  obtain ⟨A,fee,base,grant⟩:=Run.rampK hG (working.also paid) penalty hp
  exact ⟨A,fee,base,act A grant⟩

end YM.Integration.FVA1Physical.Round2.Curvature
