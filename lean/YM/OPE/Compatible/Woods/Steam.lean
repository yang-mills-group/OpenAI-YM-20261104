import YM.OPE.Compatible.Woods.Cold
/-!
# Counting stencils with the dimensional budget on fixed-factor forest.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Next.Free FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G: Gauge}{ι:Type*} {c f L:Side}{r v t: ℕ}{P:Patch}{C:KernelChoices}{η A s: ℝ}
def forestWalk (G:Gauge) (P:Cross L (TypeFace r) (TypeFace v)) : Cross L (PAC G r) (PAC G v):= fun a b i => if a.2.2=b.2 then P (a.1,a.2.1) b.1 i else 0
lemma forestWalk_read (g:Ratio c f)(P:Cross g.count (TypeFace r) (TypeFace v)) : installed g (forestWalk G P)=tensor G (installed g P):=by
   ext ⟨x,a,i⟩ ⟨y,b,j⟩; by_cases hx:i=j
   · simp only [tensor,Matrix.of_apply, if_pos hx, installed,Matrix.submatrix_apply, split_co,Row.acts,id_eq,forestWalk]
   rw [tensor]; simp [Matrix.of_apply, hx, installed,Matrix.submatrix_apply, split_co,Row.acts, forestWalk]
lemma forestWalk_pay {P:Cross L (TypeFace r) (TypeFace v)} (h:P.strip s A)(he:0≤A): (forestWalk G P).strip s A:=by
   intro x y; by_cases hx:x.2.2=y.2
   · rw [show forestWalk G P x y=P _ _ from funext fun i=>if_pos hx]; exact h _ _
   simp [forestWalk,Laurent.Width,RG.SumBudget,he,hx]
def into (G:Gauge)(L:Side): Cross L (PAC G 1) (Slip G L):= fun i j z=> unitRow _ i (bird j) z
lemma into_paid (G:Gauge)(L:Side)(s:ℝ): (into G L).strip s 1:= fun _ _=>strip_unit _ _
lemma into_good (G:Gauge)(L:Side) : Whole (into G L):=⟨1,_,one_pos, into_paid _ _ _⟩
lemma into_trunks (g:Ratio c f)(h:Odd g.count.val):
    (let F:=forest g h; let x:=squad g h G
     insertion (plant (G:=G) F) = (installed g (into G g.count)).submatrix id x):=by
     intro F X; ext i j
     rw [Matrix.submatrix_apply]
     let H := splitCo g (PAC G 1)
     change (if plant F j=i then (1:ℝ) else 0) = (unitRow _).acts c (H i) ((X j).1,bird (X j).2)
     rw [show ((X j).1,bird (X j).2)=H (plant F j) from rooting g h j, acts_unit, Matrix.one_apply] ; simp only [H.injective.eq_iff,eq_comm]
-- ok gap
namespace Medal
variable (S:StepData c f)(hp:Odd S.patch.L.val)(D:Train t)(B: Medal S.patch G S.kernel t)(hh:4≤t)
include hh B
local notation "H"=>pink S.kernel.penalty D
local notation "F" => forest S.ratio hp
local notation "X" => squad S.ratio hp G
lemma measure_pond : treeInverse G S F H 0= ((B.V D).acts c).submatrix X X := by
    have he := hedge_acts H ((heart_saves S.kernel.penalty S.kernel.penalty_pos hh (fun i:Train t=>i)).1.whole D) S hp (G:=G)
    rw [treeInverse,resolve,zero_smul,add_zero]; erw [he]
    have hw: (B.V D).acts c= _ := B.reads D c; erw [hw]; exact Matrix.inv_submatrix_equiv ..
lemma measure_pos : (treeMatrix G S F H).PosDef := by
    let Q:=forge S.patch S.kernel G D
    have he : treeMatrix G S F H=(Q.acts c).submatrix X X:= hedge_acts H ((heart_saves _ S.kernel.penalty_pos hh (fun i:Train t=>i)).1.whole D) S hp (G:=G)
    have hg : Gap (treeMatrix G S F H) B.gap:=by erw [he]; exact (B.deep D c).submatrix X (X).injective
    apply AnalyticBridge.LocalGaussianLaws.gap_positive _ hg B.root
    obtain hw:= heart_heats _ S.kernel.penalty_pos hh (fun i:Train t=> i)
    obtain ⟨v,C,hv,hC,h⟩:=hw.1.funds
    exact (Matrix.IsSymm.submatrix (A:= fullMatrix G S H) (full_symmetric H (obey_band H (hw.1.stock.whole D) (h D) f).1) (plant _))
end Medal
end YM.OPE.Woody
