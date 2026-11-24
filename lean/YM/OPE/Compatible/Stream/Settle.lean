import YM.OPE.Compatible.Stream.AxisCost
/-! Telescope right with same-exponent gain pre-prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Frequency
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate
variable {α γ:Type*} [Fintype α][Fintype γ][DecidableEq γ]
variable (R:Row α γ)(l:List Axis)(s:Axis){η c:ℝ}
omit [Fintype α] in
private lemma slew {p : Momentum}(hp:p∈baseCube) (k:Axis)(v:Whole R): (composeRows (dashAxis k R) (pathJet γ [k])).read p= R.read p-(pending k R).read p:=by
    rw [(dash_whole v k).read (jet_whole _ _) hp.1,jet_read _ _ hp.1,Matrix.mul_smul,Matrix.mul_one]
    rw [read_blank v k hp.1,show listChip p [k]=q p k by simp [switch_axis,listChip]]
    exact read_part v k hp.1
-- recursively peel; later used on acts; track zeroth
variable {R} (hη:0<η) (h:R.strip η c)
def yieldW (η:ℝ):= (Real.exp η-1)⁻¹+(1-Real.exp (-η))⁻¹
include h hη
omit [DecidableEq γ] [Fintype α] [Fintype γ] in
lemma dash_funds (i:Axis) : (dashAxis i R).strip η (yieldW η*c) := by
   intro a b; exact (advance_tariff _ hη i).released (by have h₁:=lt_sub_iff_add_lt.mpr (show 0+1 < Real.exp η by rw [zero_add]; exact Real.one_lt_exp_iff.mpr hη); have h₂:0<1-Real.exp (-η):=sub_pos.2 (Real.exp_lt_one_iff.mpr (by linarith)); positivity) (h a b) hη.le
omit [DecidableEq γ] [Fintype α] [Fintype γ] in
lemma side_funds (i:Axis): (pending i R).strip η c:= fun a b=>by simpa only [pending,one_mul] using (eval_axis η hη.le i).released zero_le_one (h a b) hη.le
-- 
lemma sputter (s:Axis) (n:Side) : R.acts n=(dashAxis s R).acts n*motion γ n [s]+(pending s R).acts n:=by
    let G:= composeRows (dashAxis s R) (pathJet γ [s]); let H:= pending s R
    have he:Whole R:=⟨η,c,hη,h⟩
    have hF:= dash_whole he s; have hL:= jet_whole γ [s]; have hH: Whole H:=⟨η,c,hη,side_funds hη h s⟩
    have hG:=hF.prod hL
    calc
      _ = (plusRows G H).acts n:= he.eq_on (hG.plus hH) (fun p hp => by rw [hG.read_plus hH hp.1,show G.read p = _ from slew R hp s he]; unfold H; rw [sub_add_cancel]) n
      _ = _ := by rw [hG.acts_plus hH,hF.acts hL]; rfl
def mutate {α γ} :Row α γ→ List Axis→ Row α γ
| A,[]=>A
| A,a::l=> mutate (pending a A) l
def selectAxis (A:Row α γ)(l:List Axis) (x:Fin l.length):Row α γ:= dashAxis (l.get x) (mutate A (l.take x))
omit [DecidableEq γ] [Fintype α] [Fintype γ] in
lemma mutate_cost : (mutate R l).strip η c:=by
   induction l generalizing R with
   | nil=>exact h
   | cons i l ih=>exact ih (side_funds hη h i)
omit [DecidableEq γ] [Fintype α] [Fintype γ] in
lemma paid_each (x:Fin l.length) : (selectAxis R l x).strip η (yieldW η*c) := dash_funds hη (mutate_cost _ hη h) _
omit [DecidableEq γ] [Fintype α] [Fintype γ] in
lemma endings (p:Momentum)(hp:p∈ baseCube): (mutate R l).read p= R.read (fun i=> if i∈l then 0 else p i):=by
   induction l generalizing R with
   | nil=>simp [mutate]
   | cons a l ih=>
     rw [mutate,ih (side_funds hη h a)]
     rw [read_blank (show Whole R from ⟨η,c,hη,h⟩)]; swap
     · rw [physical_iff]; intro i; split; simp; exact (physical_iff _).mp hp.1 _
     congr! 2 with i; by_cases h: i=a
     · subst i;simp
     simp [h]
lemma peel (n:Side) : R.acts n=(mutate R l).acts n+∑ i:Fin l.length, (selectAxis R l i).acts n*motion γ n [l.get i]:=by
    induction l generalizing R with
    | nil => simp [mutate]
    | cons a l ih=>
      let t:= pending a R
      calc
        _ = _:= sputter hη h a n
        _ = _:= by
          rw [mutate]; change _ = (mutate t l).acts n+∑ i:Fin (l.length+1), (selectAxis R (a::l) i).acts n*motion γ n [(a::l).get i]; rw [Fin.sum_univ_succ]; rw [ih (side_funds hη h a)]
          suffices hq: ∀ i: Fin l.length,selectAxis R (a::l) (i.succ) = selectAxis t l i by
             simp_rw [hq]; simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,List.getElem_cons_succ]
             rw [show selectAxis R (a::l) 0=dashAxis a R from rfl]; unfold t; abel
          intro i; unfold selectAxis; rfl -- List.take succ
lemma wholesale (n:Side) (hc:R.read 0=0) (ht:∀ i: Axis,i∈l): R.acts n=∑ i:Fin l.length, (selectAxis R l i).acts n*motion γ n [l.get i]:=by
    have hs:Whole (mutate R l):=⟨η,c,hη,mutate_cost l hη h⟩
    rw [peel l hη h n, hs.eq_on (B:=0) barren_whole, barren_acts,zero_add]
    intro p hp; rw [endings l hη h _ hp,barren_read]; simpa only [ht,if_true] using! hc
end YM.Next.Free.Frequency
