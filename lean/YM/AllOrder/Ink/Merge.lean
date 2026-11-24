import YM.AllOrder.Ink.Pill
import YM.Work.F08.Rows
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Method
open Work.F08
variable {δ:Type}
-- charge arithmetic completion official preL? we use postL.
def joinRows [Fintype δ] (X:Stalk α δ)(F:Stalk δ β) := Work.F08.composeRows X F
omit [Fintype α] [Fintype β] in
lemma weave_rows {A:Stalk α β}{B:Stalk α β}(hA:Belt A a C)(hB:Belt B a D) (ha:0≤a): Belt (minusRows A B) a (C+D) ∧ direct (minusRows A B) n=direct A n-direct B n:= ⟨strip_minus hA hB,acts_minus ha hA hB n⟩
omit [Fintype α] [Fintype β] in
lemma rolled [Fintype δ] {X:Stalk α δ}{Y:Stalk δ β}(hX:Belt X a C)(hY:Belt Y a D)(ha:0≤a) : Belt (joinRows X Y) a ((Fintype.card δ:ℝ)*(C*D)) ∧ direct (joinRows X Y) n=direct X n *direct Y n:= ⟨strip_compose ha hX hY,acts_compose ha hX hY _⟩

local notation "P"=> α⊕β
-- spine zero vertical horizontal injection
omit [Fintype α] [Fintype β] in
lemma paid_identity [DecidableEq α] (n:Side) : Belt (unitRow α) a 1 ∧ direct (unitRow α) n=1 := ⟨strip_unit, acts_unit n⟩
-- stack for projection
abbrev day (α β:Type)[DecidableEq α] : Stalk (α⊕β) α := stackRows (unitRow α) 0
omit [Fintype α] [Fintype β] in
lemma paid_day [DecidableEq α] : Belt (day α β) a 1 := max_self (1:ℝ) ▸ (strip_stack (strip_unit (α:=α)) (show Bloch.Row.strip (α:=β) (β:=α) 0 a 1 from fun i j=>by simp [Width,SumBudget]) : Belt (day α β) a _)
-- Qualifier projections. compressed α may Empty.
local notation "Ω"=>rule (α⊕β) n

-- partition vertically
lemma cut_sum {R:Type}[AddCommMonoid R](f : Leaf n P→R) : (∑ i:Leaf n P,f i)= (∑ i:Leaf n α,f (lead β i))+∑ j:Leaf n β,f (Primitives.TwoWave.peg α j) := by -- precedence issue
 rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_sum_type]; rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]; rfl
lemma tablet [DecidableEq α](x:rule α n): know (day α β) n x= mingle x 0:= by
  ext1 i; rcases i with ⟨z,i|j⟩; · exact congr_fun (show (direct (unitRow α) n*ᵥ x)=_ by rw [(paid_identity (a:=0) n).2, Matrix.one_mulVec]) (z,i)
  change (∑ i: Leaf n α,_)=_; refine Finset.sum_eq_zero ?_; intro i _; unfold direct day stackRows; simp -- maybe case motive
lemma bulbs (C: BoardL n (α⊕β) (α⊕β))(x:rule β n) (k:Leaf n (α⊕β)):
     (C*ᵥ mingle 0 x) k =∑ i:Leaf n β, C k (Primitives.TwoWave.peg α i)* x i:= by
  unfold Matrix.mulVec dotProduct; rw [cut_sum]; simp only [show ∀ i:Leaf n α,mingle (0:rule α n) x (lead β i)=0 from fun i=>rfl,mul_zero,Finset.sum_const_zero,zero_add]; rfl

lemma bank_run (F:Stalk β β)(x:rule α n)(y:rule β n): know (expand F α) n (mingle x y)=mingle 0 (know F n y):= by
  ext1 i; let H:=direct (expand F α) n; rcases i with ⟨z,i|j⟩ <;> change ∑ i:Leaf n (α⊕β),_ = _
  · apply Finset.sum_eq_zero; rintro ⟨w,l|l⟩ _ <;> simp [direct,expand,Matrix.of_apply] -- simpl syntax
  rw [cut_sum]; let r:= z; rw [Finset.sum_eq_zero ?_,zero_add]; · rfl
  intro i _; change direct (expand F α) n _ (lead β i)* mingle x y _=_; rw [direct_apply]; simp [expand, lead,Primitives.TwoWave.up]
lemma endur [DecidableEq α] (x:rule α n)(y:rule β n): know (transRows (day α β)) n (mingle x y)=x:= by
  funext i; let A:=direct (unitRow α) n; rw [show know _ _ _= (direct (day α β) n).transpose *ᵥ mingle x y from (by change direct _ n *ᵥ _= _; rw [show direct _ n= _ from (acts_trans (day α β) n)]; rfl)]; unfold Matrix.mulVec dotProduct; rw [cut_sum]; nth_rw 2 [Finset.sum_eq_zero ?_] -- bad
  · rw [add_zero]; change (A.transpose *ᵥ x) i=_; rw [show A=_ from (paid_identity (a:=0) (α:=α) n).2,Matrix.transpose_one, Matrix.one_mulVec]
  intro j _; simp [direct,day,stackRows,Primitives.TwoWave.peg,Primitives.TwoWave.up]
lemma joinKnow {δ:Type}[Fintype δ](U:Stalk α δ)(V:Stalk δ β)(h:Belt U a C)(H:Belt V a D)(ha:0≤a)(v:rule β n): know (joinRows U V) n v=know U n (know V n v):= by
 change (direct _ n*ᵥ v)=direct U n*ᵥ (direct V n*ᵥ v); rw [mulVec_mulVec,(rolled (n:=n) h H ha).2]
variable (A:Stalk (α⊕β) (α⊕β))(V:Stalk β β)(X:rule α n) (Y:rule β n)[DecidableEq α][DecidableEq β]
def outlook (α β:Type)[Fintype α][DecidableEq α]: Stalk (α⊕β) (α⊕β):= joinRows (day α β) (transRows (day α β)) -- horiz projection
local notation "O"=>outlook α β
omit [Fintype β] in
lemma paid_out (α β:Type)[Fintype α][DecidableEq α](ha:0≤a) : Belt (outlook α β) a ((Fintype.card α:ℝ) *(1*1)):= (rolled (n:= Primitives.TwoWave.RealSlice.three) (α:=α⊕β) (β:=α⊕β) paid_day (strip_trans paid_day) ha).1
lemma looks_at (ha:0≤a): know (O) n (mingle X Y)= mingle X 0:= by unfold outlook; rw [joinKnow _ _ (paid_day (a:=a)) (show Belt _ a 1 from strip_trans (η:=a) paid_day) ha,endur,tablet]
def applyM := minusRows (unitRow (α⊕β)) (joinRows (expand V α) (joinRows A (O)))
def billH (α β:Type)[Fintype α][Fintype β] (C D:ℝ):ℝ:= 1+(Fintype.card (α⊕β):ℝ)*(D*((Fintype.card (α⊕β):ℝ)*(C*((Fintype.card α:ℝ)*(1*1)))))
abbrev booth (x: rule (α⊕β) n) : rule β n:= here Sum.inr x
abbrev lay (x:rule (α⊕β) n) : rule α n:= here Sum.inl x
noncomputable def wagon (W:rule α n)(B: BoardL n (α⊕β) (α⊕β)): rule β n:= booth (B*ᵥ mingle W 0)
variable (ha:0≤a)(h:Belt A a C)(H:Belt V a D)(hD:0 ≤ D)
include h ha H hD
lemma rentM : Belt (applyM A V) a (billH α β C D) ∧ know (applyM A V) n (mingle X Y)=mingle X (Y-know V n (wagon X (direct A n))) := by
 let U:= joinRows A (O); let Q:= expand V α; let E:=joinRows Q U; let P':=unitRow (α⊕β)
 have hu:= rolled (n:=n) h (paid_out α β ha) ha; let hx:= weave_rows (n:=n) (paid_identity (a:=a) (α:=α⊕β) n).1 (rolled (n:=n) (bank H α hD) hu.1 ha).1 ha; refine ⟨hx.1,?_⟩; let W:=mingle X Y; let y:=mingle X (0:rule β n); let z:=know A n y
 change (direct (minusRows P' E) n*ᵥ W)=_; rw [hx.2, Matrix.sub_mulVec]; rw [(paid_identity (a:=0) (α:=α⊕β) n).2, Matrix.one_mulVec]; change W-know E n W=_; have hE:know E n W=mingle 0 (know V n (booth z)):= by rw [joinKnow _ _ (bank H α hD) hu.1 ha] ; rw [joinKnow _ _ h (paid_out α β ha) ha, looks_at X Y ha]; calc
     _ = know Q n (mingle (lay z) (booth z)):= congr_arg (⇑(know (expand V α) n)) (pair_mingle z).symm
     _ = _ := bank_run ..
 rw [hE]; ext1 i; rcases i with ⟨i,j|j⟩; · exact sub_zero ..
 rfl
end Method
end YM.AllOrder.Ink
