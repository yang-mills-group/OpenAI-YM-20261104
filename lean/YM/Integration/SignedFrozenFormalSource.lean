import YM.Integration.SignedFormalPowerLayers
import YM.Integration.ActualOriginalQFrozenInput

/-! The independently prescribed original RG02 marked vertex on the physical ultraviolet coefficient columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedFrozenFormalSource
open Function Filter Set Finset Lattice Wilson RG Source Labels Marker Multi Precision Tree Exterior
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Comparison.RG02.Order NativePaidPacketColors MergeProof MergeProof.Accent
open scoped BigOperators Classical Topology ContDiff

section Constant
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {D : V→ ComparisonDensity.Address.Orbit}
    {P : MarkedPackets D G f R} {p : BudgetPoint} {ad : V→ Support f}
    {reg : Comparison.Density.Testing.Region (fun v=>(D v).Mood) f} {w : V→ℝ} {g width budget : ℝ} {off slope : ℕ}
    (H : P.Paid p ad reg w g width budget off slope) (hg : g≠0) (hP : P.powerCap=0)
    {h : Clip} {path : PathData G} {O : ChartRatio G} (K : Bulk.Kernel S h path O)

include H hg hP in
/-- A physically frozen marked source has no artificial one-order shift left in its native perturbative field. -/
theorem remove (vac : ℝ→ Config G f→ℝ) (x : TestSpace D) (s : Hot R) (B : fieldDir G c 1) (n : ℕ) :
    Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (Bulk.markFn S F (colors P vac x) s) (1+n)=
      Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (fun v : Bulk.Joint S F (G:=G)=>
        (P.read x 1 (Work.F03.live F v.2)).part s.val) n := by
  have hs : powers P={0} := by simp [powers,hP]
  have h0 : SignedFormalPowerLayers.fiber F P x s 0=fun v : Bulk.Joint S F (G:=G)=>
        (P.read x 1 (Work.F03.live F v.2)).part s.val := by
    funext v
    have h := read_mode_sum H hg s.val ((hot_iff_ne _).1 s.property) x 1 (Work.F03.live F v.2)
    simpa [SignedFormalPowerLayers.fiber,hs] using h.symm
  have hf := SignedFormalPowerLayers.kernel F H hg K vac x s B n
  simpa [commonPower,hP,hs,h0] using hf
end Constant

variable {G : Gauge} {run : Run G} {deck : MS.Local.Physical.Deck G} {p L n : ℕ} {hn : n≤L}
    {V : Type} [DecidableEq V] [Fintype V] (Q : MS.Land.Prescription deck)
    (D : ActualRunQlocalNativeTuple.Datum run p L n hn V) (u : V→ MS.Rake.Label deck) (μ : ℝ) (orders : V→ℕ)
    {c : Side} {S : StepData c (run.family.side L p)} (F : Forest S.ratio)
    {h : Clip} {path : PathData G} {O : ChartRatio G} (K : Bulk.Kernel S h path O)
local notation "Orbit" => ActualRunQlocalNativeTuple.orbit D
local notation "P₀" => ActualOriginalQFrozenInput.packets Q D u μ orders
local notation "Γ" => Stock.census V

/-- The original calibrated physical columns, each retaining its independent external test, true running field scale and independently prescribed static MS charges, in the same physical geometry. -/
def columns (x : TestSpace Orbit) (s : Hot Γ) (v : Bulk.Joint S F (G:=G)) : ℂ :=
  (Mach Γ (fun i=>ActualRunQlocalNativeTuple.reader D i (x i) *
    ActualOriginalCalibratedColumns.weightedObservable run deck Q (u i) μ (run.family.side L p)
      (ActualRunQlocalNativeTuple.root D i) (Work.F03.live F v.2) (orders i))).part s.val

theorem kernel (N : ℕ) (hL : L≤N) (point : BudgetPoint) (w : V→ℝ) (width : ℝ) (hw : ∀i,0<w i)
    (hwidth : 0<width) (vac : ℝ→ Config G (run.family.side L p)→ℝ) (x : TestSpace Orbit) (s : Hot Γ)
    (B : fieldDir G c 1) (j : ℕ) :
    Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (Bulk.markFn S F (colors (P₀ N) vac x) s) (1+j)=
      Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (columns Q D u μ orders F x s) j := by
  have H := ActualOriginalQFrozenInput.packets_paid Q D u μ orders N 1 point w width hwidth hw
  rw [remove F H one_ne_zero (show (P₀ N).powerCap=0 by rfl) K vac x s B j]
  apply congrArg (fun v : Bulk.Joint S F (G:=G)→ℂ=>Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) v j)
  exact funext (fun v=>congrArg (fun b : Poly Γ=>b.part s.val)
    (ActualOriginalQFrozenInput.packets_read Q D u μ orders N hL 1 x (Work.F03.live F v.2)))

/-- The finite native charged generator, including every added coupling slot, on the actual original ultraviolet columns before the independent Fk covariance contraction. -/
theorem generator (N : ℕ) (hL : L≤N) (point : BudgetPoint) (w : V→ℝ) (width : ℝ) (hw : ∀i,0<w i)
    (hwidth : 0<width) (vac : ℝ→ Config G (run.family.side L p)→ℝ) (x : TestSpace Orbit)
    (B : fieldDir G c 1) (q : S.Choices) (r : ℕ) (s : Hot (Order.Board Γ r)) (hs : (Join.left s.val).val.Nonempty) :
    let j := (Join.right s.val).val.card
    let i : Hot Γ := ⟨Join.left s.val,hs⟩
    let W := colors (P₀ N) vac x
    Assembly.generator (Bulk.stage K F B) (Bulk.hinge F) W.power (Bulk.markFn S F W) (Bulk.geometric K F q W) r s=
      (j.factorial:ℂ) • Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (columns Q D u μ orders F x i) j := by
  dsimp only [Assembly.generator]
  rw [dif_pos hs]
  exact congrArg ((_:ℂ) • ·) (kernel Q D u μ orders F K N hL point w width hw hwidth vac x ⟨Join.left s.val,hs⟩ B (Join.right s.val).val.card)

end YM.Integration.SignedFrozenFormalSource
