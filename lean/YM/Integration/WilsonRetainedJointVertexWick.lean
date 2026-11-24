import YM.Integration.WilsonRetainedJointVertexFiling
import YM.Integration.WilsonCoherentMayerFuelSquare
import YM.Integration.WilsonOriginalSignedSamplerMoment

/-! The independent finite earlier Wilson action on the actual physical forest.
Every tree coordinate is fixed and every surviving link uses its enrolled free coordinate. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic FreeResolvent PowerSeries
open WilsonCoherentMayerHearing Dict06.Series
open scoped BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

private def linkOf (b : Woods G f) : Bond f := (b.1,axisEquiv.symm b.2.1)

private def coordinate (X : Coat T F) (b : Woods G f) : Normal.poly (Eye X) :=
  if h : linkOf b ∈ F.trunks then 0 else WilsonCoherentMayerFuelPolynomial.coordinate X (linkOf b) h b.2.2

private theorem readCoordinate (X : Coat T F) (b : Woods G f) (z : Air f G) :
    Cloud.paint (fun i => z (tube X i)) (coordinate X b) =
      (((cloth G f) (angularSample F z)) b : ℂ) := by
  have actual : ((cloth G f) (angularSample F z)) b =
      if linkOf b ∈ F.trunks then 0 else z (linkOf b, b.2.2) := by
    change (WilsonCoherentMayerNoise.row F z (linkOf b)) b.2.2 = _
    unfold WilsonCoherentMayerNoise.row
    split <;> rfl
  rw [actual]
  by_cases h : linkOf b ∈ F.trunks
  · simp [coordinate, h]
  · rw [coordinate, dif_neg h, if_neg h, WilsonCoherentMayerFuelPolynomial.read_coordinate]

/-- Express each filed real field polynomial in the original free-link variables. -/
def forestPolynomial (X : Coat T F) :
    MvPolynomial (Woods G f) ℝ →+* Normal.poly (Eye X) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Complex.ofRealHom) (coordinate X)

theorem forest_read (X : Coat T F) (z : Air f G) (p : MvPolynomial (Woods G f) ℝ) :
    Cloud.paint (fun i => z (tube X i)) (forestPolynomial X p) =
      (MvPolynomial.eval ((cloth G f) (angularSample F z)) p : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [forestPolynomial, Cloud.paint]
  | add p q hp hq => simp only [map_add, hp, hq, Complex.ofReal_add]
  | mul_X p u hp =>
    have hu : forestPolynomial X (MvPolynomial.X u) = coordinate X u :=
      MvPolynomial.eval₂Hom_X' _ _ _
    simp only [map_mul, hu, hp, readCoordinate, MvPolynomial.eval_X, Complex.ofReal_mul]

/-- A finite product of the filed earlier action coefficients on this one torus. -/
def filedPolynomial {I : Type*} [Fintype I] (X : Coat T F) (a : I → PrismA G)
    (q : I → ℕ) (g p : ℝ) : Normal.poly (Eye X) :=
  ∏ i, MvPolynomial.C ((Comparison.RG02.Integral.temperature g*p*
        (g/Real.sqrt p)^((a i).grade-(a i).rise) : ℝ) : ℂ) *
    ∑ r ∈ range (q i + 1), MvPolynomial.C ((g:ℂ)^r) *
      forestPolynomial X (coeff ((a i).grade-(a i).rise+r) (PowerSeries.X^2 * flash (Mosaic.surf (a i) f)))

theorem filed_read {I : Type*} [Fintype I] [DecidableEq I] (X : Coat T F) (Z : SeriesA G)
    {σ D : ℝ} (hs : 0<σ) (draw : Draw Z σ D) (a : I → PrismA G) (enrolled : ∀ i, a i ∈ Z)
    (q : I → ℕ) (g p : ℝ) (z : Air f G) :
    let weight := fun i => Comparison.RG02.Integral.temperature g*p*(g/Real.sqrt p)^((a i).grade-(a i).rise)
    Cloud.paint (fun i => z (tube X i)) (filedPolynomial X a q g p) =
      ∑ x : I → Site f, ∏ i, (weight i : ℂ) * siteTaylor (a i).cells (x i) (angularSample F z) (q i) g := by
  intro weight
  rw [filed_words Z hs draw a enrolled (angularSample F z) q g p]
  have scalar (b : ℂ) : Cloud.paint (fun i => z (tube X i)) (MvPolynomial.C b) = b := by simp [Cloud.paint]
  simp only [filedPolynomial, map_prod, map_mul, map_sum, scalar, forest_read]

variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}
    {R : Rep G f}

/-- Compare the complete retained old placement polynomial times any common registered
marked polynomial with the independently prescribed Gaussian, including its cut error. -/
theorem filed_wick {I : Type*} [Fintype I] [DecidableEq I]
    (H : Cash W s μ L Q o C T R) (temp : 0 ≤ Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (Z : SeriesA G) {σ D : ℝ} (hs : 0<σ) (draw : Draw Z σ D)
    (a : I → PrismA G) (enrolled : ∀ j, a j ∈ Z) (q : I → ℕ) (g p : ℝ) :
    let F := Greenbelt.allot i
    let X := chamber T s o.K χ 1 v i tag
    let weight := fun j => Comparison.RG02.Integral.temperature g*p*(g/Real.sqrt p)^((a j).grade-(a j).rise)
    ∀ B : Normal.poly (Eye X),
      let J := B * filedPolynomial X a q g p
      let held := fun z : Air f G => Cloud.paint (fun u => z (tube X u)) B *
        ∑ x : I → Site f, ∏ j, (weight j : ℂ) * siteTaylor (a j).cells (x j) (angularSample F z) (q j) g
      Integrable held X.dice ∧
        ‖(∫ z, held z ∂X.dice) - Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
            (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 J‖ ≤
          Rise.coin J * WilsonOriginalSignedSamplerMoment.fee T L P o J.totalDegree s := by
  intro F X weight B J held
  have read (z : Air f G) : held z = Cloud.paint (fun u => z (tube X u)) J := by
    dsimp only [held, J]
    rw [map_mul, filed_read X Z hs draw a enrolled q g p z]
  have manifest : X.manifest := by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have meas := (WilsonCoherentMayerFuelSquare.sampled X A.fullC J).1
  have price := WilsonOriginalSignedSamplerMoment.original T H temp χ v i tag J J.totalDegree le_rfl
  have he : held = fun z => Cloud.paint (fun u => z (tube X u)) J := funext read
  rw [he]
  exact ⟨meas, price⟩

end YM.Integration.OriginalMarkedRunAction

