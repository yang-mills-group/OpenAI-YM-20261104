import YM.Integration.WilsonCoherentMayerSectorWarning

/-! The original entered finite Mayer team, including every old paid
activity and all fresh signs, at the actually used positive decoration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerFuelEntered
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


open WilsonRetainedStencilMoment ProbabilityTheory
attribute [local instance] Gauge.frobInner
variable (run:Run G) {I:Type} [Fintype I] (ds:I→ℕ)

open WilsonCoherentMayerMixedMoment
open WilsonCoherentMayerSignedCharge (residual)


open WilsonCoherentMayerFuelPolynomial (label)
open WilsonCoherentMayerFuelWick (word)
open WilsonCoherentMayerFuelGate (weight)


open WilsonPositionSeparatedProfileMayerStencilPrice (deposited budget)


open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences
open WilsonPositionSeparatedProfileMayerMasks (gates)
open WilsonPositionSeparatedProfileMayerGateSafety (sites)
open WilsonPositionSeparatedProfileMayerGateReturn (source bank)
open private measurable layers from YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn
open WilsonCoherentMayerFuelSector (patch)

theorem absent (q:Ledger f 2) (old:Team R):label (S:=S) q∉old.signs S:=by
  intro z
  obtain ⟨m,_,same⟩:=Finset.mem_image.mp z
  cases h:m.turn <;> simp [h,Wing.badge,WilsonCoherentMayerFuelPolynomial.label] at same

theorem purchased (entry:Submitted run R I) (old:Team R) (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
    (X:Coat T F) (H:Cash W X.x μ L Q o C T R) (fitted:X.width=o.K) (manifest:X.manifest)
    (flat:X.blank=X) (stamped:Stamp T) (q:Ledger f 2) (first:q.2.1∉F.trunks)(last:arrive q.2.1 q.2.2∉F.trunks)
    {M:ℕ}(u:Mayer.Decors (WilsonCoherentMayerFuelSector.patch (S:=S) q (together entry old fresh) \ (together entry old fresh).signs S) M):
    let prior:=together entry old fresh
    let k:=Mayer.decorOrder u
    let saved:=fun z:momentSpace X=>source entry old o.a X z*((Mayer.exponent H (X.wrapY z.1) z.2 (label q))^k/k.factorial)
    let delta:=fun z:momentSpace X=>(Mayer.planned H (WilsonCoherentMayerFuelSector.patch q prior) u (Laminate.partner prior H) X z:ℂ)-(saved z:ℝ)
    Integrable delta (moment X) ∧ (∫z,‖delta z‖ ∂moment X)≤
      bank entry old * ((((Coat.capQ S o.eta o.gap o.ample (tubularPrice G L) X.B G 1 q)^k/k.factorial)*
        Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L)) (2*(2*k))))*
        Real.sqrt (X.dice.real (eerie X (sites entry T X.x) o.ξ R.beta))):=by
  intro prior k saved delta
  let D:=eerie X (sites entry T X.x) o.ξ R.beta
  let source0:=source entry old o.a X
  let gate (z:momentSpace X):=∏i,gates entry i o.a X z
  let e:=WilsonCoherentMayerFuelGate.weight X q R.beta o.a k
  let test (z:momentSpace X):=source0 z*(gate z-1)*e z.2
  have income:=measurable entry old H.laws.data.funds.funds o.a X flat
  have mtest:Measurable test:=((income.1.mul (income.2.sub measurable_const)).mul
    ((WilsonCoherentMayerFuelRemoval.borel X q R.beta o.a k).comp measurable_snd))
  have hb:0≤bank entry old:=(norm_nonneg _).trans (WilsonPositionSeparatedProfileMayerGateReturn.bound entry old o.a X (1,0))
  have bounded (z:momentSpace X):|test z|≤bank entry old:=by
    have rg:gate z∈Set.Icc 0 1:=layers entry o.a X z
    have rq:e z.2∈Set.Icc 0 1:=WilsonCoherentMayerFuelGate.range ..
    have gap:|gate z-1|≤1:=abs_le.mpr ⟨by linarith [rg.1],by linarith [rg.2]⟩
    rw [show test z=source0 z*(gate z-1)*e z.2 from rfl,abs_mul,abs_mul,abs_of_nonneg rq.1]
    calc _ ≤ bank entry old*1*1 := by
           apply mul_le_mul _ rq.2 rq.1 (by positivity)
           exact mul_le_mul (WilsonPositionSeparatedProfileMayerGateReturn.bound entry old o.a X z) gap (abs_nonneg _) hb
         _ = _:=by ring
  have off (z:momentSpace X) (notin:z.2∉D):test z=0:=by
    have eq:gate z=1:=Finset.prod_eq_one fun i _=> WilsonPositionSeparatedProfileMayerGateSafety.clear entry X H fitted manifest flat stamped z.1 z.2 notin i
    simp [test,eq]
  let B:=word X q first last k (1:Normal.poly (Eye X))
  have hd:B.totalDegree≤2*k:=by
    simpa using WilsonCoherentMayerFuelWick.degree X q first last k 0 (1:Normal.poly (Eye X)) (by simp)
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl fitted manifest
  have paid:=WilsonCoherentMayerSectorWarning.measured X A B (2*k) hd D (measurable_eerie ..) test mtest hb bounded off
  have eq:delta=(fun z:momentSpace X=>(test z:ℂ)*Cloud.paint (fun i=>z.2 (tube X i)) B):=by
    funext z
    have subset:prior.signs S⊆WilsonCoherentMayerFuelSector.patch q prior:=Finset.subset_insert ..
    have read:=WilsonCoherentMayerFuelSector.issued (p:=WilsonCoherentMayerFuelSector.patch q prior) q u (WilsonCoherentMayerFuelSector.appended q prior (absent q prior)) H (Laminate.partner prior H) X z
    rw [Laminate.compartments prior _ subset,WilsonPositionSeparatedProfileMayerMasks.products entry old fresh] at read
    have issued:=WilsonCoherentMayerFuelWick.incidence X q first last H k (1:Normal.poly (Eye X)) z.2
    rw [map_one,mul_one] at issued
    dsimp only [delta,saved,source0,test,gate,B,e]
    rw [read,WilsonCoherentMayerFuelHaar.sampled H X rfl flat manifest z.1 z.2 q]
    push_cast
    rw [show (((Mayer.exponent H X z.2 (label q):ℝ):ℂ)^k/(k.factorial:ℂ))=
      ((WilsonCoherentMayerFuelGate.weight X q R.beta o.a k z.2:ℝ):ℂ)*
      Cloud.paint (fun i=>z.2 (tube X i)) B from by unfold WilsonCoherentMayerFuelGate.weight;push_cast at issued ⊢;exact issued]
    unfold WilsonPositionSeparatedProfileMayerGateReturn.source
    push_cast;ring
  rw [eq]
  have cost:=WilsonCoherentMayerFuelTariff.repeated X A q first last k (1:Normal.poly (Eye X))
  have single:Rise.coin (1:Normal.poly (Eye X))=1:=by
    rw [show (1:Normal.poly (Eye X))=MvPolynomial.C 1 from (map_one MvPolynomial.C).symm,Rise.coin,Rise.pay_C,norm_one]
  rw [single,mul_one] at cost
  refine ⟨paid.1,paid.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cost (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hb

end YM.Integration.WilsonCoherentMayerFuelEntered
