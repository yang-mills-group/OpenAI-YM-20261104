import YM.AllOrder.Iron.Poise
import YM.Next.STATIONARY.Block.Static
import YM.TraceExtension.Perfect.Stove
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

open Work.F05
local notation "C"=> cash (helmets G c f)
local notation "W"=> Cou G c f
variable (i: G.ColorIndex)
local notation "J"=> Bodies G c f
open Wilson Precision
-- price envelope. row norm via resulting decay
variable {t} (hp: S.patch.Branches S.kernel G)
include hp
local notation "L"=> S.ratio.count.val
local notation "R"=> S.patch.radius
local notation "H"=> (shear (fedora S t) (1:Joint G c f))
lemma borrow (i:Lines G c 0)(j:Lines G f 1): H (.inr i) (.inl j)=(if i.2.2=j.2.2 then fixRoot S (i.1,i.2.1) (j.1,j.2.1) else 0):= by
 let D:=t; rw [shear,bill_def,show helmets G c f (Sum.inl j)=((pocket _) j,0) from (by simp [helmets]),tailor_arch t hp,helmets,cash_prod_right, cash_pocket, zero_add]
 rcases i with ⟨p,r,l⟩; rw [vac_only r]; let E:=Trace.Perfect.armament S (1:Joint G c f); change uniformM (fixRoot S) (pocket (Lines G f 1) j) _= _
 have he:= Trace.Perfect.candry (S:=S) j p (1:Joint G c f); dsimp only at he; rw [Trace.Perfect.armament_one, Trace.Perfect.road_one,G.adjoint_one] at he
 have hh(k'): edgeColor (Trace.Perfect.desk j) (Trace.Perfect.edgeOf (j.1,j.2.1)) k'= (if k'=j.2.2 then (1:ℝ) else 0):= by rw [Trace.Perfect.edge_parts]; rcases j with ⟨_,_,_⟩; simp [Trace.Perfect.desk, Pi.single_apply]
 have ht := congr_arg (fun x:G.Color=> x l) he
 rw [show (pocket (Lines G f 1) j)=Trace.Perfect.desk j from (by simp [Trace.Perfect.desk])]
 refine ht.trans ?_; simp only [PiLp.smul_apply, smul_eq_mul,hh]; split<;> simp [*]
lemma shear_pay (i j:J) : (R*12+1 < separation (addressJ S i) (addressJ S j)→ H i j=0)∧ |H i j| ≤ 16*R+1:= by
 let V:= S.ratio.parent; let B:= (1:Joint G c f); have ha (i : Lines G f 1) : helmets G c f (Sum.inl i)=((pocket _) i,0) := by simp [helmets];
 have hb (i : Lines G c 0) : helmets G c f (Sum.inr i)=(0,(pocket _) i) := by simp [helmets]
 have hx {x:Site c} : ¬R*12+1< separation x x:=by rw [separation_self]; omega
 cases i with
 | inl i=>
    cases j with
    | inl j=> rw [shear,bill_def,ha,helmets,cash_prod_left,tailor_arch t hp,cash_pocket]; change (_→ pocket (Lines G f 1) j i=0)∧|pocket (Lines G f 1) j i| ≤ _; by_cases hd : i=j
              · refine ⟨fun he=> False.elim ?_,?_⟩; simp [hd] at he; simp [hd]
              simp [hd]; positivity
    | inr j=> rw [shear, bill_def,hb,helmets,cash_prod_left,tailor_arch t hp]; simp [cash_pocket]; positivity
 | inr i=>
    rcases i with ⟨p,i,a⟩; rw [vac_only i]; cases j with
    | inl j=> rw [borrow hp]; split
              · have he:= Trace.Perfect.fix_meter S p (j.1,j.2.1); refine ⟨fun hh=> he.2 ?_, le_trans he.1 (le_add_of_nonneg_right (by norm_num))⟩; rw [addrR,addrL] at hh; change S.patch.radius *12+1<separation p (V j.1) at hh; have hr:= Work.E04.parent_separation S.ratio (S.ratio.embed p) j.1; rw [Ratio.embed_parent] at hr; change _ < separation _ j.1; unfold V at hh; omega
              constructor
              · intros; rfl
              rw [abs_zero]; positivity
    | inr j=> rw [shear, bill_def,hb,helmets,cash_prod_right,tailor_arch t hp,cash_pocket]; change (_→ ((pocket (Lines G c 0) j)+uniformM (fixRoot S) (0:Link G f)) (p,vac,a)=0)∧|((pocket (Lines G c 0) j)+uniformM (fixRoot S) (0:Link G f)) (p,vac,a)| ≤ _; rw [map_zero,add_zero]; by_cases hd : (p,vac,a)=j;
              · refine ⟨fun he=> False.elim ?_,?_⟩; rw [hd,separation_self] at he; omega; simp [hd]
              simp [hd]; positivity
end YM.AllOrder.Iron
