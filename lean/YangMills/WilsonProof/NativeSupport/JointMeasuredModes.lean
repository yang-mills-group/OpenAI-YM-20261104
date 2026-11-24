import YangMills.WilsonProof.NativeSupport.JointOwnerSheets

/-! All original nonempty one-owner or owner-free modes of the selected nonlinear sheet. -/
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
variable (p:B.Mode)
variable (old : ∀ i,(q i).s=p → marks (.inl i)=∅)

include origin in
omit [DecidableEq I] in
private theorem empty_probe_sum (away : Disjoint p.val active) (u:I → ℂ) :
    (∑ i:I,u i*(sing (q i) w).part p)=0 := by
  apply sum_eq_zero
  intro i _
  have ne:p ≠ (q i).s := by
    rintro rfl
    obtain ⟨v,have₁,have₂⟩:=origin i
    exact disjoint_left.mp away have₁ have₂
  rw [Menu.sing,Poly.part_send,if_neg ne,mul_zero]

include h hw origin old in
theorem all_old_modes (hot:p ≠ B.quiet) (short:(p.val∩active).card ≤ 1) :
    (∀ X U,(spine L₀ Y χ marks test fees B painted X U).part p =
      ∑ i:I,(Photo.spine L₀ Y χ fees (Stock.census Unit) (probe i) X U).part oneName*(sing (q i) w).part p) ∧
    (∀ X U,(Photo.chain A K B painted X U).part p =
      ∑ i:I,(Photo.chain A K (Stock.census Unit) (probe i) X U).part oneName*(sing (q i) w).part p) := by
  by_cases hit:(p.val∩active).Nonempty
  · obtain ⟨v,one⟩:=card_eq_one.mp (le_antisymm short (card_pos.mpr hit))
    exact ⟨measured_spine_owner q w hw Y χ A marks test K h active origin p v one old,
      measured_chain_owner q w hw Y χ A marks test K h active origin p v one⟩
  have away : Disjoint p.val active := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hit)
  constructor
  · intro X U
    rw [empty_probe_sum q w active origin p away]
    have whole := (Towed.repair (flag_E L₀ Y χ A marks test fees K B painted h w hw (fun i=>Menu.paid (heap q i) hw)) hw U).2
    exact tally_without_owner q w active origin p (fun z:Y.fragrances=>Y.bookFoot (.inr z)) (tones L₀ Y χ marks test fees) X U away hot whole
  · intro X U
    rw [empty_probe_sum q w active origin p away]
    have whole := (Towed.repair (Photo.flag_K A K B painted w hw (fun i=>Menu.paid (heap q i) hw) h.gas A.p.exponent_pos.le) hw U).2
    exact tally_without_owner q w active origin p (barcode A.activities) (fun j Z t s=>K t s j Z) X U away hot whole

end YM.Integration.InletSusceptibility.SelectedKernel
