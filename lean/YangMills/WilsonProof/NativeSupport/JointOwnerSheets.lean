import YangMills.WilsonProof.NativeSupport.JointSingleScores
import YangMills.WilsonProof.NativeSupport.JointOwnerTally

/-! The inherited single-owner component of the full measured regular
and forced sheets at a physical visit. All countable summability input
comes from that visit's original measured purchase. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.SelectedKernel
open Merge Merge.Photo JointLeaves
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open NativeSwitch MergeProof MergeProof.Menu MergeProof.Accent Marker
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V] {B : Census V}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T:Tube G S} {R:Rep G f}
variable {W x μ C : ℝ} {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (q : I → Hat B R) (w:V→ℝ) (hw:∀ i,0<w i) (Y:Cash W x μ L Q o C T R) (χ:Chi) (A:Rep G c)
local notation "L₀" => (fun i : Mound q=>(heap q i).M)
local notation "fees" => (fun i : Mound q=>sumFee (heap q i) w)
local notation "painted" => (fun i : Mound q=>sing (heap q i) w)
local notation "probe" i => singleProbe (Sum.inl i : Mound q)
local notation "oneName" => (Stock.census Unit).fire ()
variable (marks : Mound q → Finset (Bond c)) (test : Mound q → Bond c → ℝ → ℝ)
variable (K : ℝ → Finset (Mound q) → Code G c) {dk ex kr : ℝ}
variable (h : Usable (fun i : Mound q=>(heap q i).M) Y χ A marks test (fun i : Mound q=>sumFee (heap q i) w) K dk ex kr)
variable (active : Finset V) (origin : ∀ i,∃ v∈(q i).s.val,v∈active)
variable (p:B.Mode) (y:V) (only : p.val∩active={y})
variable (old : ∀ i,(q i).s=p → marks (.inl i)=∅)

private def uniformProbe {J:Type} (i:J) := singleProbe i

private theorem probe_agrees {J:Type} [DecidableEq J] (i:J) : singleProbe i=uniformProbe i :=
  congrArg (fun d : DecidableEq J => @singleProbe J d i) (Subsingleton.elim _ _)

private theorem small {J:Type} [DecidableEq J] (i j:J) :
    Poly.price (fun _ : Unit=>1) (singleProbe i j)≤1 := by
  by_cases hji : j=i <;> simp [singleProbe,hji,Poly.toll]

include h hw origin only old in
theorem measured_spine_owner (X:Support c) (U:Config G c) :
    (spine L₀ Y χ marks test fees B painted X U).part p =
      ∑ i:I,(Photo.spine L₀ Y χ fees (Stock.census Unit) (probe i) X U).part oneName*(sing (q i) w).part p := by
  have whole := (Towed.repair (flag_E L₀ Y χ A marks test fees K B painted h w hw (fun i=>Menu.paid (heap q i) hw)) hw U).2
  have one i := (Towed.repair (flag_E L₀ Y χ A marks test fees K (Stock.census Unit) (probe i)
    h (fun _=>1) (fun _=>zero_lt_one) (small _)) (fun _=>zero_lt_one) U).2
  rw [show (spine L₀ Y χ marks test fees B painted X U).part p =
      ∑ i:I,(spine L₀ Y χ marks test fees (Stock.census Unit) (probe i) X U).part oneName*(sing (q i) w).part p from
    tally_one_owner q w active origin p y only (fun z:Y.fragrances=>Y.bookFoot (.inr z))
      (tones L₀ Y χ marks test fees) X U whole one]
  apply sum_congr rfl
  intro i _
  by_cases mode : (q i).s=p
  · rw [probe_agrees (Sum.inl i : Mound q)]
    exact congrArg (fun f : Support c → Config G c → Poly (Stock.census Unit) =>
        (f X U).part oneName*(Menu.sing (q i) w).part p) (inherited_spine L₀ Y χ marks test fees (Sum.inl i : Mound q) (old i mode))
  · rw [Menu.sing,Poly.part_send,if_neg (Ne.symm mode),mul_zero,mul_zero]

include h hw origin only in
theorem measured_chain_owner (X:Box c) (U:Config G c) :
    (Photo.chain A K B painted X U).part p =
      ∑ i:I,(Photo.chain A K (Stock.census Unit) (probe i) X U).part oneName*(sing (q i) w).part p := by
  have whole := (Towed.repair (Photo.flag_K A K B painted w hw (fun i=>Menu.paid (heap q i) hw) h.gas A.p.exponent_pos.le) hw U).2
  have one i := (Towed.repair (Photo.flag_K A K (Stock.census Unit) (probe i) (fun _=>1) (fun _=>zero_lt_one)
    (small _) h.gas A.p.exponent_pos.le) (fun _=>zero_lt_one) U).2
  exact tally_one_owner q w active origin p y only (barcode A.activities) (fun j Z t s=>K t s j Z) X U whole one

end YM.Integration.InletSusceptibility.SelectedKernel
