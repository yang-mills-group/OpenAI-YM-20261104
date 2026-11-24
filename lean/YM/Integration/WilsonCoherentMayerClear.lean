import YM.Integration.WilsonCoherentMayerField
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.CutGerm
import YM.LocalLTE.Fan.Chair

/-! The surviving all-elastic component carries the original empty store.
Its saved field disappears at every sampled orbit, before testing any
global flags of the held coarse configuration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerClear
open Function Lattice RG Pressure Tree Wilson Finset Precision
open ConnectedActivityE6 Shell Coat Matter RGLocalTaylor.Insert
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}

theorem eligible (X:Coat T F) (h:Assembly.Clear S X.x X.seeds F) (e:F.Free) : X.Hot e.val := by
  refine ⟨e.property,not_not.mpr (Finset.disjoint_left.mpr ?_)⟩
  intro y hy ey
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp ey
  rcases Finset.mem_insert.mp hv with h₁|h₁
  · subst v
    exact h e (Or.inl hy)
  · rw [Finset.mem_singleton.mp h₁] at hy
    exact h e (Or.inr hy)

theorem base (X:Coat T F) (h:Assembly.Clear S X.x X.seeds F) :
    X.input 0=replica S.ratio X.V:=by
  rw [←lifted F X.V]
  apply congrArg F.drape
  funext i
  change X.view 0 i=G.lieExp ((0:F.Free→G.Color) i)*replica S.ratio X.V i.val
  simp [Coat.view,eligible X h i,RG.increment]

theorem prepped (X:Coat T F) (v:Finset (LocalLTE.Fan.Veil c f)) (tag:S.Choices) (y:F.Slice G) :
    (((Matter.preps X (roster (LocalLTE.Fan.arm (S:=S) v))).taggedL tag).wrapY y).input 0=
      replica S.ratio X.V := by
  apply base
  change Assembly.Clear S X.x (roster (LocalLTE.Fan.arm (S:=S) v)) F
  rw [LocalLTE.Fan.Field.rosterD]
  exact Assembly.bare_is_Clear S X.x F

variable (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)

theorem at_one (X:Coat T F) (hx:X.V=1) (v:Finset (LocalLTE.Fan.Veil c f)) (tag:S.Choices)
    (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site f) (β:ℝ)
    (z:momentSpace ((Matter.preps X (roster (LocalLTE.Fan.arm (S:=S) v))).taggedL tag)) :
    let Y:= (Matter.preps X (roster (LocalLTE.Fan.arm (S:=S) v))).taggedL tag
    WilsonCoherentMayerField.written R d θ y o Y β z =
      ∏ i, Dict06.Wil.book (R.family.localSection (d i))
        ((R.family.labels.level (d i)).scaled θ⁻¹ (y i))
        (expandAt (o i) (WilsonCoherentMayerField.direction (Y.wrapY z.1) β z.2)) := by
  dsimp only
  unfold WilsonCoherentMayerField.written
  dsimp only
  rw [prepped X v tag z.1,hx,replica_one]
  exact Finset.prod_congr rfl fun i _=>WilsonCoherentAffineBook.flat _ _ _

end YM.Integration.WilsonCoherentMayerClear
