import YM.Integration.ActualNormalizedRayJets
import YM.Integration.NativePaidPacketColors
import YM.Integration.FullQLocalNumericStepData
import YM.Comparison.RG02.Valence.Amplify

/-! The divided physical mark determines all mixed source jets, even when the two clearing powers differ. -/
noncomputable section
namespace YM.Integration.WilsonNormalizedMarkedSource
open Function Filter Finset RG Precision Lattice Wilson Exterior Tree Marker Multi
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Assembly Comparison.RG02.Cumulants
open PertExtension.Series Next.SectorChange LocalComparison
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

section comparison
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

private theorem ordered {a b : ℕ} {f g : ℝ×E → W} (hf : GradeAt a f) (hg : GradeAt b g)
    (u : E) (hba : b ≤ a) (h : ∀t : ℝ,t ≠ 0 →
      (t^a)⁻¹ • f (t,t • u)=(t^b)⁻¹ • g (t,t • u)) (k : ℕ) :
    jet f (a+k) (1,u)=jet g (b+k) (1,u) := by
  let e (t : ℝ) := g (t,t • u)
  have he : ContinuousAt e 0 := hg.smooth.continuousAt.comp_of_eq
    (continuousAt_id.prodMk (continuousAt_id.smul continuousAt_const)) (by simp)
  have lift : ∀ᶠ t in 𝓝[≠] (0:ℝ), e t=(t^(a-b))⁻¹ • f (t,t•u) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hn : t ≠ 0 := by simpa using ht
    have eq1 := h t hn
    calc
      e t = (t^b) • ((t^b)⁻¹ • g (t,t•u)) := by rw [smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hn),one_smul]
      _ = (t^b) • ((t^a)⁻¹ • f (t,t•u)) := by rw [eq1]
      _ = _ := by rw [smul_smul];congr 1;rw [show t^a=t^b*t^(a-b) from by rw [←pow_add];congr 1;omega];field_simp [hn]
  have shifted := ActualNormalizedRayJets.joint_coefficient (hf.lower (Nat.sub_le _ _)) u he lift (b+k)
  have hz := ActualNormalizedRayJets.joint_coefficient (hg.lower (Nat.zero_le _)) u he
    (Eventually.of_forall fun t=>by simp [e]) (b+k)
  have hsum : a-b+(b+k)=a+k := by omega
  rw [hsum] at shifted
  exact shifted.symm.trans (by simpa using hz)

theorem coefficients {a b : ℕ} {f g : ℝ×E → W} (hf : GradeAt a f) (hg : GradeAt b g)
    (u : E) (h : ∀t : ℝ,t ≠ 0 →
      (t^a)⁻¹ • f (t,t•u)=(t^b)⁻¹ • g (t,t•u)) (k : ℕ) :
    jet f (a+k) (1,u)=jet g (b+k) (1,u) := by
  rcases le_total b a with hba|hab
  · exact ordered hf hg u hba h k
  · exact (ordered hg hf u hab (fun t ht=>(h t ht).symm) k).symm
end comparison

section original
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  {V : Type} [DecidableEq V] [Fintype V] {R : Census V} (K : Bulk.Kernel S p P O) (F : Forest S.ratio)
variable (W D : Bulk.Colors R G f) (hW : Bulk.Well W) (hD : Bulk.Well D)
variable (hraw : ∀t : ℝ,t ≠ 0 →∀U : Config G f,Integral.markedLog t U W=Integral.markedLog t U D)

omit [Fintype V] in
include hW hD hraw in
theorem source (x : fieldDir G c 1) (i : Hot R) (k : ℕ) :
    Assembly.kernelJet (Bulk.stage K F x) (Bulk.hinge F) (Bulk.markFn S F W i) (W.power i+k) =
    Assembly.kernelJet (Bulk.stage K F x) (Bulk.hinge F) (Bulk.markFn S F D i) (D.power i+k) := by
  apply Valence.Enlist.paint_inj
  intro z
  rw [Assembly.reading,Assembly.reading]
  change jet (Bulk.markFn S F W i) _ (Bulk.translated K F x z)=jet (Bulk.markFn S F D i) _ (Bulk.translated K F x z)
  rw [Bulk.footing]
  apply coefficients (Bulk.joint_receipt S F (hW.suppose_mark i)) (Bulk.joint_receipt S F (hD.suppose_mark i))
  intro t ht
  let a : Bulk.SliceDir S F G := (x,fderiv ℝ (K.b F) 0 x + tape z)
  have h := congrArg (fun a : Poly R=>a.part i.val) (hraw t ht (Work.F03.live F (t • a)))
  simpa only [Integral.markedLog,part_lit,Bulk.markFn,Bulk.posed] using h

include hW hD hraw in
theorem generator (tag : S.Choices) (hv : W.vac=D.vac) (x : fieldDir G c 1) (r : ℕ) :
    Assembly.generator (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W) (Bulk.geometric K F tag W) r =
    Assembly.generator (Bulk.stage K F x) (Bulk.hinge F) D.power (Bulk.markFn S F D) (Bulk.geometric K F tag D) r := by
  have hgeom : Bulk.geometric K F tag W=Bulk.geometric K F tag D := by
    funext z
    simp only [Bulk.geometric,Bulk.fee,Bulk.supplement,hv]
  funext i
  dsimp only [Assembly.generator]
  split_ifs with h
  · exact congrArg ((_:ℂ) • ·) (source K F W D hW hD hraw x ⟨_,h⟩ _)
  · rw [hgeom]

include hW hD hraw in
theorem formal (tag : S.Choices) (hv : W.vac=D.vac) (x : fieldDir G c 1) (r : ℕ) :
    Bulk.Fk K F tag W x r=Bulk.Fk K F tag D x r := by
  unfold Bulk.Fk Assembly.prescription
  rw [generator K F W D hW hD hraw tag hv x r]
end original

section canonical
open LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {C : Family G}
  {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C R} (I : AnalyticInput J A d)
  (Y : Bulk.Chain C.path) (x : TestSpace J.tests)
local notation "S" => C.path.levels.clock.op d.level d.period
local notation "g₀" => Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1)

def genuine := NativePaidPacketColors.colors I.packets (I.colors x).vac x

/-- The exact same original independently tested formal output, with the actual finite input packet power. -/
theorem evaluated (hg : g₀ ≠ 0) (F : Forest (S).ratio) (tag : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (r : ℕ) :
    Bulk.Fk (d.kernel Y) F tag (I.colors x) B r=Bulk.Fk (d.kernel Y) F tag (genuine I x) B r := by
  have w := I.convention.well x
  have w' := NativePaidPacketColors.colors_well I.input_paid hg (I.colors x).vac w.suppose_vac w.natural w.envelope x
  apply formal _ F (I.colors x) (genuine I x) w w' ?_ tag rfl
  intro t ht U
  rw [I.convention.marks x t ht U]
  exact (NativePaidPacketColors.colors_markedLog I.input_paid hg (I.colors x).vac x t ht U).symm

/-- The true regulator coupling on every admitted step supplies the nonvanishing denominator. -/
theorem selected (hC : C.Makes) (F : Forest (S).ratio) (tag : (S).Choices)
    (B : fieldDir G (C.side d.level d.period) 1) (r : ℕ) :
    Bulk.Fk (d.kernel Y) F tag (I.colors x) B r=Bulk.Fk (d.kernel Y) F tag (genuine I x) B r :=
  evaluated I Y x (IterationFour.Currency.g_pos hC d.cutoff d.period _ d.below).ne' F tag B r

/-- Literal finite derivative order of the newly identical canonical marked term. -/
theorem genuine_power (q : Hot R) : (genuine I x).power q=I.packets.powerCap+1 := rfl
end canonical
end YM.Integration.WilsonNormalizedMarkedSource
end
