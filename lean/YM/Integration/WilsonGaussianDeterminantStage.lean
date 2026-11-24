import YM.Integration.WilsonReportingDecoratedStage
import YM.Integration.WilsonGaussianDeterminantVolume

/-! Before a reporting run chooses a period or a physical conductor, buy the
actual normalized determinant and its marked jets at every prescribed stage order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantStage
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

open WilsonGaussianDeterminantRoster WilsonGaussianDeterminantFull PhysicalAffineScalarLogarithm
open RGLocalTaylor LocalTaylorR2.Pavilion

def precision (k : ℕ) : ℝ := ((k:ℝ)+1)⁻¹

def mode (G : Gauge) (L : Side) (s : ℝ) : ℝ := betaF G s L ^ (-(1/2:ℝ))

def Bought (χ : Chi) (H : Cash W s μ L Q o C T R) (p j k : ℕ) : Prop :=
  (∀ i : Bond f, Sees H j (mode G L s) (mode G L s) χ
      (fun _ X _ => fullPair X i - seed X i - model p R X i) (precision k*(gStep R.beta)^p) 1) ∧
  Sees H j (mode G L s) (mode G L s) χ
    (fun _ X _ => WilsonGaussianDeterminantVolume.scalar X - ∑ i, (seed X i + model p R X i))
    ((Fintype.card (Bond f):ℝ) * (precision k*(gStep R.beta)^p)) 1

private theorem shape {D E : Patch} (length : D.L=E.L) (stage : D.J=E.J) : D=E := by
  cases D; cases E; cases length; cases stage; rfl

def decal (G : Gauge) (χ : Chi) : Decal G where
  rub P Q _ L W μ o _ i x := ∀ p ≤ i, ∀ j ≤ i, ∀ k ≤ i,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f) (C : ℝ)
      (H : Cash W x μ L Q o C T R), Bought χ H p j k
  good P Q _ := by
    refine ⟨0,fun L _ W μ o _ i _ _ _ => ?_⟩
    by_cases existsPatch : ∃ D : Patch, D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    · obtain ⟨D,hD,len,stage⟩ := existsPatch
      have v : Rate G L (-(1/2)) (mode G L) := Rate.power
      have hv : ∀ᶠ s : ℝ in atTop, 0 ≤ mode G L s :=
        ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun s hs => Real.rpow_nonneg hs.le _
      have price (p j k : Fin (i+1)) := by
        have hε : 0 < precision k.val := by unfold precision; positivity
        exact (WilsonGaussianDeterminantPhysical.original P Q o L D hD χ p.val j.val (mode G L) (mode G L)
          v hv _ hε).and (WilsonGaussianDeterminantVolume.original P Q o L D hD χ p.val j.val (mode G L)
          (mode G L) v hv _ hε)
      have booked := eventually_all.mpr (fun p => eventually_all.mpr
        (fun j => eventually_all.mpr (fun k => price p j k)))
      filter_upwards [booked] with x paid p hp j hj k hk c f S T R C H
      have funds := H.laws.data.funds
      have same := shape (funds.length_eq.trans len.symm) (funds.funds.atStep.trans stage.symm)
      have h := paid (⟨p,Nat.lt_succ_of_le hp⟩ : Fin (i+1)) (⟨j,Nat.lt_succ_of_le hj⟩ : Fin (i+1))
        (⟨k,Nat.lt_succ_of_le hk⟩ : Fin (i+1))
      exact ⟨fun a => h.1 c f S T R μ C H a same,h.2 c f S T R μ C H same⟩
    · exact Eventually.of_forall fun _ _ _ _ _ _ _ _ _ S _ _ _ H => False.elim
        (existsPatch ⟨S.patch,H.laws.data.funds.funds.kernel,H.laws.data.funds.length_eq,
          H.laws.data.funds.funds.atStep⟩)

def joined {V : Type} [DecidableEq V] [Fintype V] (G : Gauge) (J : FullQLocal.RenderedStep.Request V)
    (χ : Chi) : Decal G := (WilsonReportingDecoratedStage.joined G J χ).paired (decal G χ)

end YM.Integration.WilsonGaussianDeterminantStage
