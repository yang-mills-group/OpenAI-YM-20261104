import YM.Integration.WilsonCoherentMayerFuelMarket
import YM.Integration.WilsonPositionSeparatedProfileMayerMarketCalendar

/-! A stage chosen before every finite torus, old representation and true
tree placement pays the full measured repeated-quadratic comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerFuelThermal
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonPositionSeparatedProfileMayerWickInputs WilsonRetainedSignedStencilTaylor
open WilsonCoherentMayerHearing Dict06.Series




open LocalTaylorR2.Exponent WilsonCoherentMayerFuelGate

open WilsonCoherentMayerFuelPolynomial

private theorem squareRoot {a:ℝ} {E:ℝ→ℝ} (rate:Rate G L (2*a) E):
    Rate G L a (fun x=>Real.sqrt (2*|E x|)):=by
  intro b hb
  filter_upwards [(rate.mul_left 2) (2*b) (by linarith), (Work.E09.betaF_growth G L).eventually_ge_atTop (0:ℝ)] with x upper pos
  change |2*E x|≤betaF G x L^(2*b) at upper
  rw [abs_mul,abs_of_nonneg (by norm_num:0≤(2:ℝ))] at upper
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_sqrt upper).trans_eq
  rw [mul_comm (2:ℝ),Real.rpow_mul pos,Real.rpow_two,Real.sqrt_sq (Real.rpow_nonneg pos _)]

theorem purchased (P:Teller G) (L:Side) (D₀:Patch) {W:ℝ} (o:Target.Order G W)
    (k d:ℕ) (ε:ℝ) (ep:0<ε):
    ∀ᶠs:ℝ in atTop,∀ {c f:Side} {S:StepData c f} (T:Tube G S)
      {R:Rep G f} {Q:ConnectedActivityE6.Target G P} {μ C:ℝ} (H:Cash W s μ L Q o C T R),
      S.patch=D₀→S.patch.L=L→0≤Pressure.temp s→
      ∀(χ:Chi) (v:Finset (LocalLTE.Fan.Veil c f)) (i:Greenbelt.Reserve S) (tag:S.Choices),
      let X:=chamber T s o.K χ 1 v i tag
      let F:=Greenbelt.allot i
      ∀(q:Ledger f 2) (first:q.2.1∉F.trunks) (last:arrive q.2.1 q.2.2∉F.trunks)
        (B:Normal.poly (Eye X)),B.totalDegree≤d→
        ‖(∫z:Air f G, (((Mayer.exponent H X z (label q))^k/k.factorial:ℝ):ℂ)*
            Cloud.paint (fun a=>z (tube X a)) B ∂X.dice) -
          Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
            (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0
              (WilsonCoherentMayerFuelWick.word X q first last k B)‖ ≤
          ((Coat.capQ S o.eta o.gap o.ample (tubularPrice G L) X.B G 1 q)^k/k.factorial * Rise.coin B) *
            (ε*(Coat.gStep R.beta)^(2*k+d)) := by
  let n:=2*k+d
  let a:=Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L)) (2*n))
  have ab:0≤a:=Real.sqrt_nonneg _
  obtain ⟨E,rate,tariff⟩:=WilsonPositionSeparatedProfileMayerGateSafety.tariff P L o (2*(-(n:ℝ)-1))
  have hr:=squareRoot rate
  have fees:=WilsonPositionSeparatedProfileMayerMarketCalendar.original P L D₀ o n _ hr a 1 0 le_rfl ε ep
  filter_upwards [tariff,fees] with s sold ticket
  intro c f S T R Q μ C H patch side temp χ v i tag X F q first last B deg
  have manifest:X.manifest:=by
    change (ConnectedActivityE6.Matter.roster (LocalLTE.Fan.arm (S:=S) v)).flags = RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  have gate:=sold.2 H X rfl rfl manifest (sites (S:=S) q)
  have ears:(sites (S:=S) q).card*E s≤2*|E s|:=by
    apply (mul_le_mul_of_nonneg_left (le_abs_self (E s)) (Nat.cast_nonneg _)).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast WilsonCoherentMayerFuelGate.count (S:=S) q) (abs_nonneg _)
  have charge:=ticket T H patch side
  simp only [one_mul,zero_mul,add_zero,abs_mul,abs_of_nonneg ab,abs_of_nonneg (Real.sqrt_nonneg _)] at charge
  have supply:=WilsonCoherentMayerFuelMarket.original H temp χ v i tag q first last k d B deg
  apply supply.trans
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have coin:0≤Rise.coin B:=by rw [Rise.metal];positivity
  have cap:0≤Coat.capQ S o.eta o.gap o.ample (tubularPrice G L) X.B G 1 q:=
    by
      have h:=WilsonCoherentMayerFuelTariff.acquired X A q
      have positive:0≤WilsonCoherentMayerFuelTariff.charge X q:=by
        unfold WilsonCoherentMayerFuelTariff.charge
        positivity
      exact positive.trans h
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (gate.trans ears)) ab) (le_refl _)).trans charge

end YM.Integration.WilsonCoherentMayerFuelThermal
