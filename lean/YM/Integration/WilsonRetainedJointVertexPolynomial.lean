import YM.Integration.WilsonRetainedJointVertexWeightedChamber
import YM.Integration.WilsonRetainedJointVertexMarkPower

/-! The same measured old-action replacement holds for the original Wick test polynomial. -/
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

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
    {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W} {R : Rep G f}

theorem chamber_polynomial (H : Cash W s μ L Q o C T R) (temp : 0 ≤ Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) (n K : ℕ)
    (σ D : Fin (n+1) → ℝ) (hs : ∀ j, 0 < σ j) (filed : ∀ j, Draw Z (σ j) (D j))
    (a : Fin (n+1) → PrismA G) (member : ∀ j, a j ∈ Z) (x : Fin (n+1) → Site f)
    (g p : ℝ) (hg : 0 < g) (small : g ≤ 1) (lo : 1/2 ≤ p) (hi : p ≤ 3/2) :
    let F := Greenbelt.allot i
    let X := WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let β := Comparison.RG02.Integral.temperature g
    let w := fun j => β*p*(g/Real.sqrt p)^((a j).grade-(a j).rise)
    let old := fun (j : Fin (n+1)) (z : Air f G) =>
      (w j : ℂ)*sitePacket (a j).cells (x j) ((X.wrapY y).input ((X.wrapY y).liftA β z))
    let row := fun (j : Fin (n+1)) (z : Air f G) =>
      (w j : ℂ)*siteTaylor (a j).cells (x j) (angularSample F z) ((a j).rise+K+1) g
    let cost := fun j r => occurrencePrice G L o.eta o.gap o.ample (σ j) (D j) (a j) r (n+2)
    ∀ B : Normal.poly (Eye X),
      let certificate := Rise.coin B*(1+Real.sqrt (Common.priced (1+payE o.eta o.gap o.ample (tubularPrice G L))
           (2*((n+2)*B.totalDegree))))
      let difference := fun z : Air f G => Cloud.paint (fun u => z (tube X u)) B *
        ((∏ j, row j z)-∏ j, old j z)
      Integrable difference X.dice ∧
        ‖∫ z, difference z ∂X.dice‖ ≤
          certificate*((2:ℝ)^(n+2)*g^(K+∑ j, (a j).grade)*
            ∏ j, max (cost j (a j).rise) (cost j ((a j).rise+K))) := by
  intro F X β w old row cost B certificate difference
  have manifest : X.manifest := by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) F).bowed temp
  obtain ⟨A,-,-,-⟩:=H.laws.data.localP F X rfl rfl manifest
  obtain ⟨pos, measurable, moment⟩ := mark_power X A B (n+1)
  exact chamber_marked H temp χ v i tag y Z n K σ D hs filed a member x g p hg small lo hi
    (fun z => Cloud.paint (fun u => z (tube X u)) B) pos measurable moment

end YM.Integration.OriginalMarkedRunAction

