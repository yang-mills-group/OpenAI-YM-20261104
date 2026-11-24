import YM.RegulatorIR.Calibration.Upright

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Calibration
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {X:Type} {M:X→ℕ}{n:Page M→Side}(S:Circuit M n) {K:KernelChoices}(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G)(c: G.ColorIndex)
local notation "Q"=> S.payroll Y G Z
local notation "N"=> Notebook S Y G Z
local notation "T₁"=> S.scroll_j Y G
variable {s t: Tent M} {D: Choice M}{p e:ℕ} (H:Notebook S Y G Z c D s p)
lemma returns (T:Scale) : biases T 0=1:= (tale_base).trans T.stable
include H
lemma shrinks (h:e≤p): Notebook S Y G Z c D s e:=⟨fun i=> ⟨fun j hj=> (H.clean i).1 j (hj.trans h),fun j hj=> (H.clean i).2 j (hj.trans h)⟩,H.reference ⟩
lemma recognized (F:Notebook S Y G Z c D t p) : ∀ i : Page M, Squares p (tale (sheet s i|>.beta)) (tale (sheet t i|>.beta)):=by
 induction p with
 | zero=>intro i j hj; rw [show j=0 by omega]; exact (returns _).trans (returns _).symm
 | succ p ih=>
    let a:= sheet s; let b:=sheet t
    have h:=ih (shrinks S Y G Z c H (Nat.le_succ _)) (shrinks S Y G Z c F (Nat.le_succ _))
    have hx(i: Page M): Matches p ((Q a).bulk i) ((Q b).bulk i):=bulk_comms S Y G Z _ i fun j _=> h j
    let d(i:Page M):= biases (a i) (p+1)-biases (b i) (p+1); let ν(i:X):=d (Page.opening M i)
    have hp(i:Page M): biases (a i) (p+1)=biases (b i) (p+1) +d i:=by unfold d; ring
    have ht : ∀ i:Page M,d i = ν i.bindW∧ (Q a).bulk i (p+1)= (Q b).bulk i (p+1)+Warm.peak (d i • coil (T₁ i)):=by
       refine Page.proves (fun i=>⟨rfl,top_h _ _ _ _ _ _ (hp _) (h _)⟩) ?_
       intro i hi; let v:= d i.prev; have ht:= chests S Y G Z a i (hp i.prev) (h _) (hx i.prev) hi.2; have hv : d i.next=v:=by
          have hf:= increases S Y G Z a c i.next ht; unfold d v; rw [← show _=biases (a i.next) _ from (H.clean i.next).1 (p+1) le_rfl (by omega), ←show _=biases (b i.next) _ from (F.clean i.next).1 (p+1) le_rfl (by omega)]; change Rules.token ((Q a).bulk _ _ 2) c- Rules.token ((Q b).bulk _ _ 2) c=_; rw [hf,add_sub_cancel_left]
       exact ⟨hv.trans hi.1,hv ▸ ht⟩
    have he(i:X) : ν i=0:=by
       let p':=D.choose i
       have hf : a p'=b p':=congr_arg Feeds.scale ((H.reference i).trans (F.reference i).symm)
       rw [← show d p'=ν i from (ht p').1]; unfold d; rw [hf,sub_self]
    intro i j hj;by_cases hy:j=p+1
    · subst j;change biases (a i) _=biases (b i) _;rw [hp i,(ht i).1,he,add_zero]
    exact h i j (by omega)
lemma coloring (hG:G.Simple)(d:G.ColorIndex): Notebook S Y G Z d D s p:=by
 refine ⟨fun i=>⟨fun j hj he=>?_, (H.clean i).2⟩,H.reference⟩
 let A:=sheet s; let X:= (Q A).bulk i j 2; let z:Room:=step 0
 rw [← (H.clean i).1 j hj he]; obtain ⟨t,hv⟩:= Rules.solar_eq (Stage.ort_T S Y G Z A hG i j he) (cost_token S Y G Z A i j) z hG 1
 have ht(c:G.ColorIndex): Rules.token X c=t:=by
    let v:=EuclideanSpace.basisFun G.ColorIndex ℝ; change Pupil.shine X 2 z (1,c) (1,c)=t; rw [← Rules.shade_raw,hv (v c) (v c),show inner ℝ (v c) (v c)=1 from v.inner_eq_one _,mul_one]
 exact (ht d).trans (ht c).symm
-- pulse.B.Clock exports all order germ records.Never use across different patches unless adapting.
lemma uniques (he:Notebook S Y G Z c D t p) (i:Page M) : Matches p ((Q (sheet s)).bulk i) ((Q (sheet t)).bulk i):=bulk_comms S Y G Z _ _ fun j _=> recognized S Y G Z c H he j -- remove h
end YM.RegulatorIR.Calibration
