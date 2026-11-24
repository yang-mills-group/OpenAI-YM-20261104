import YM.Integration.WilsonRetainedSiteWickWord
import YM.Integration.WilsonRetainedJointVertexWick

/-! Compare the true retained Wilson action product and a correlated marked
polynomial to the independent Wick rule at the same named sites. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open Census Window
open scoped BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W} {R : Rep G f}

def occupiedPolynomial {I : Type*} [Fintype I] (X : Coat T F) (a : I → PrismA G) (x : I → Site f)
    (K : ℕ) (g p : ℝ) (B : Normal.poly (Eye X)) : Normal.poly (Eye X) :=
  B * ∏ j, rootedSite X (a j) (x j) K g p

theorem occupied_fees {I : Type*} [Fintype I] (X : Coat T F) (a : I → PrismA G)
    (x : I → Site f) (σ D : I → ℝ) (hs : ∀ j, 0<σ j) (filed : ∀ j, Commission (a j).cells (σ j) (D j) (a j).grade)
    (K : ℕ) (g p : ℝ) (B : Normal.poly (Eye X)) (hg : 0<g) (lo : 1/2≤p) (hi : p≤3/2) :
    let J := occupiedPolynomial X a x K g p B
    J.totalDegree ≤ B.totalDegree + ∑ j, ((a j).rise+K+1) ∧
    Rise.coin J ≤ Rise.coin B * ∏ j, rootedSiteMass (a j) (σ j) (D j) K g := by
  intro J
  have b0 : 0≤Rise.coin B := by rw [Rise.metal]; positivity
  constructor
  · apply (MvPolynomial.totalDegree_mul ..).trans
    apply Nat.add_le_add_left
    apply (MvPolynomial.totalDegree_finsetProd ..).trans
    exact Finset.sum_le_sum fun j _ => rooted_site_degree X (a j) (hs j) (filed j) (x j) K g p
  · apply (Rise.funds 0 zero_le_one _ _).trans
    apply mul_le_mul_of_nonneg_left _ b0
    apply (Rise.purchased 0 zero_le_one _ _).trans
    apply Finset.prod_le_prod
    · intro j _; exact Rise.sign 0 _ zero_le_one
    · intro j _; exact rooted_site_price X (a j) (hs j) (filed j) (x j) K g p hg lo hi

theorem occupied_wick (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) (n K : ℕ)
    (σ D : Fin (n+1) → ℝ) (hs : ∀ j, 0<σ j) (filed : ∀ j, Draw Z (σ j) (D j))
    (a : Fin (n+1) → PrismA G) (member : ∀ j, a j ∈ Z) (x : Fin (n+1) → Site f)
    (g p : ℝ) (hg : 0<g) (small : g≤1) (lo : 1/2≤p) (hi : p≤3/2) :
    let F := Greenbelt.allot i
    let X := chamber T s o.K χ 1 v i tag
    let β := Comparison.RG02.Integral.temperature g
    let old := fun (j : Fin (n+1)) (z : Air f G) =>
      (siteWeight (a j) g p : ℂ)*sitePacket (a j).cells (x j) ((X.wrapY y).input ((X.wrapY y).liftA β z))
    let cost := fun j r => occurrencePrice G L o.eta o.gap o.ample (σ j) (D j) (a j) r (n+2)
    ∀ B : Normal.poly (Eye X),
      let J := occupiedPolynomial X a x K g p B
      let observed := fun z : Air f G => Cloud.paint (fun u => z (tube X u)) B*∏ j, old j z
      let order := B.totalDegree+∑ j, ((a j).rise+K+1)
      let charge := (2:ℝ)^(n+2)*g^(K+∑ j, (a j).grade) * ∏ j, max (cost j (a j).rise) (cost j ((a j).rise+K))
      let coef := 1+Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L)) (2*((n+2)*B.totalDegree)))
      let fee := WilsonOriginalSignedSamplerMoment.fee T L P o order s
      Integrable observed X.dice ∧
      ‖(∫ z, observed z ∂X.dice) -
        Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
          (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 J‖ ≤
        Rise.coin B * ((∏ j, rootedSiteMass (a j) (σ j) (D j) K g)*|fee| + coef*charge) := by
  intro F X β old cost B J observed order charge coef fee
  let reading := fun (q : Normal.poly (Eye X)) (z : Air f G) => Cloud.paint (fun u => z (tube X u)) q
  let model := fun (j : Fin (n+1)) (z : Air f G) => (siteWeight (a j) g p : ℂ)*
    siteTaylor (a j).cells (x j) (angularSample F z) ((a j).rise+K+1) g
  let diff := fun z : Air f G => reading B z*((∏ j, model j z)-∏ j, old j z)
  have incoming (j) := (filed j).2 (a j) (member j)
  have paid : Integrable diff X.dice ∧ ‖∫ z, diff z ∂X.dice‖ ≤ (Rise.coin B*coef)*charge :=
    chamber_polynomial H temp χ v i tag y Z n K σ D hs filed a member x g p hg small lo hi B
  have manifest : X.manifest := by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  have typed : Integrable (reading J) X.dice := (WilsonCoherentMayerFuelSquare.sampled X A.fullC J).1
  have raw (z : Air f G) : reading J z = reading B z*∏ j, model j z := by
    dsimp only [reading, J, occupiedPolynomial]
    rw [map_mul, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact rooted_site_read X (a j) (hs j) (incoming j) (x j) K g p z
  have same : observed = fun z => reading J z-diff z := by
    funext z
    rw [raw]
    dsimp only [observed, diff, reading]
    ring
  have balance := occupied_fees X a x σ D hs incoming K g p B hg lo hi
  let expected := Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
    (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0 J
  have ideal : ‖(∫ z, reading J z ∂X.dice)-expected‖ ≤ Rise.coin J*fee :=
    WilsonOriginalSignedSamplerMoment.original T H temp χ v i tag J order balance.1
  have correct : ‖(∫ z, reading J z ∂X.dice)-expected‖ ≤
      (Rise.coin B*∏ j, rootedSiteMass (a j) (σ j) (D j) K g)*|fee| :=
    ideal.trans ((mul_le_mul_of_nonneg_left (le_abs_self fee)
      (show 0≤Rise.coin J from by rw [Rise.metal]; positivity)).trans
        (mul_le_mul_of_nonneg_right balance.2 (abs_nonneg fee)))
  rw [same]
  refine ⟨typed.sub paid.1, ?_⟩
  rw [integral_sub typed paid.1]
  change ‖((∫ z, reading J z ∂X.dice)-(∫ z, diff z ∂X.dice))-expected‖ ≤ _
  rw [sub_right_comm]
  exact (norm_sub_le ..).trans ((add_le_add correct paid.2).trans_eq (by ring))

end YM.Integration.OriginalMarkedRunAction

