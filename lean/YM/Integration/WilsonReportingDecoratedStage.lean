import YM.Integration.WilsonRetainedDecoratedIntegral
import YM.Integration.WilsonRootedJointCalendar

/-! Before a reporting run chooses a period or a physical conductor, buy the
actual decorated moment for every order up to the already appointed stage. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingDecoratedStage
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Port RGLocalTaylor RGLocalTaylor.Insert RGLocalTaylor.Mayer
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Daisy.Charity.RG12
open WilsonRetainedMiniatureTaylor WilsonRetainedDecoratedWord
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {P:Teller G}
    {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W} {R:Rep G f}

/-- Absolute error for the original whole Haar--Gaussian word on the cash
actually opened, along with the single rooted miniature price on that cash. -/
def Bought (χ:Chi) (H:Cash W s μ L Q o C T R) (p:ℕ):Prop :=
  ∃ w:Miniature c f→ℝ,
    Sales (radiusB s) Q.relative Q.ε (sleeve S (radiusB s) Q.halo) w (fun _=>0)
      (betaF G s L ^ (-((p:ℝ)+1-1/2)/2)) ∧
    ∀ (A:Team R) (team:Molecule S), A.signs S ⊆ team →
      ∀ (start:Start (team\A.signs S)) (M:ℕ) (u:Decors (team\A.signs S) M)
        (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K → X.manifest → X.χ=χ →
        Healthy (Pressure.temp s) (H.unionP team) X.V →
        let error z:=Mayer.planned H team u (Laminate.partner A H) X z-
          model H p team start u (Laminate.partner A H) X z
        Integrable error (moment X) ∧ (∫z,|error z| ∂moment X)≤
          A.weight*(book u (H.w+carry w) start-book u H.w start)

private theorem shape {D E:Patch} (length:D.L=E.L) (order:D.J=E.J):D=E:=by
  cases D; cases E; cases length; cases order; rfl

/-- A chart and a temperature are fixed before the period and before all
physical decorated tests. The field order used in each purchase is the
upper stage's true finite allowance. -/
def decal (G:Gauge) (χ:Chi) : Decal G where
  rub P Q _ L W μ o _ i x:=∀ p ≤ i, ∀ (c f:Side) (S:StepData c f) (T:Tube G S) (R:Rep G f) (C:ℝ)
    (H:Cash W x μ L Q o C T R), Bought χ H p
  good P Q E:=by
    refine ⟨0,fun L _ W μ o _ i _ _ _=>?_⟩
    by_cases existsPatch:∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    · obtain ⟨D,branched,len,order⟩:=existsPatch
      have zero : Rate G L (-(1/2)) (fun _=>0):=by
        intro a _
        filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 0] with s hs
        simpa using Real.rpow_nonneg hs.le a
      have presold:=eventually_all.mpr (fun p:Fin (i+1)=>
        WilsonRetainedDecoratedIntegral.purchased P Q o L D branched χ p.val 0 (1/2) (by norm_num)
          (fun _=>0) (fun _=>0) zero zero (Eventually.of_forall fun _=>le_rfl))
      filter_upwards [presold] with x sold p fits c f S T R C H
      have h:=H.laws.data.funds
      exact sold (⟨p,Nat.lt_succ_of_le fits⟩:Fin (i+1)) c f S T R μ C H
        (shape (h.length_eq.trans len.symm) (h.funds.atStep.trans order.symm))
    · exact Eventually.of_forall fun _ _ _ _ _ S _ _ _ H=>False.elim
        (existsPatch ⟨S.patch,H.laws.data.funds.funds.kernel,H.laws.data.funds.length_eq,H.laws.data.funds.funds.atStep⟩)

/-- This single booking is opened before any physical period. -/
def joined {V:Type} [DecidableEq V] [Fintype V] (G:Gauge) (J:FullQLocal.RenderedStep.Request V) (χ:Chi):Decal G:=
  (WilsonRootedJointCalendar.scheme G J).paired (decal G χ)

end YM.Integration.WilsonReportingDecoratedStage
