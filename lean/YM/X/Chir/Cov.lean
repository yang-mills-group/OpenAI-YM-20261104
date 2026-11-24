import YM.X.Chir.Curb
/-! # characteristic kernels and cumulant carries -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}
variable (i j:Axis)(p c:Tet)(r t:ℝ)
/-- Difference second leg; raises grid degree. -/
def ds (i:Axis) : Module.End ℝ Scaff where
    toFun f n x y:= f n x (y+step i)-f n x y; map_add' a b:= by ext1 n; ext x y; exact add_sub_add_comm ..
    map_smul' a b:=by ext1 n; ext x y; exact (mul_sub a ..).symm
lemma ds_val (f:Scaff) (x y:Site n): ds i f n x y=f n x (y+step i)-f n x y:= rfl
lemma graph_d (l:List Axis)(t:Cover): ds i (graphS l t) = -(graphS (i::l) (t-step i)):= by
   apply cast_inj; rw [map_neg,cast_graph]; ext n x y; change graphS _ _ n _ (wrap n y+step i)-graphS _ _ n _ (wrap n y)=_; rw [← wrap_step n i,← map_add]; change castG (graphS _ _) n x (y+step i)-castG (graphS _ _) n x y=_; rw [cast_graph,slopeY]; rfl
lemma graph_alt (l:List Axis)(t:Cover) : graphS (i::j::l) t=graphS (j::i::l) t:= by ext n x y; simp only [graphS,Interval.grads,differ]; rw [add_right_comm _ (step i)]; ring -- Step differ n
-- local span induction later
def transfer (r:ℝ)(p:Tet)(i:Axis): Scaff:= ∑ x:Axis, form r p x i • graphS [x] 0
def exchangeF (r:ℝ)(p:Tet)(t:ℝ)(c:Tet) : Scaff:= ∑ i:Axis,∑ x:Axis, form t c x i • ds x (transfer r p i)
lemma transfer_air : transfer r p i ∈ air 1:= Submodule.sum_mem _ (fun b _=> (air 1).smul_mem _ (air_graph _ 0 rfl))
lemma exchange_air : exchangeF r p t c∈ air 2:= by unfold exchangeF transfer; simp_rw [map_sum,map_smul,graph_d]; refine (air 2).sum_mem (fun i _=> (air 2).sum_mem fun x _=> (air 2).smul_mem _ ((air 2).sum_mem (fun j _=> (air 2).smul_mem _ ((air 2).neg_mem (air_graph _ _ rfl)))))
lemma transfer_val (x y:Site n): transfer r p i n x y=∑ j:Axis,form r p j i*graphS [j] 0 n x y:= by simp only [transfer, Finset.sum_apply, Pi.smul_apply,smul_eq_mul]
lemma skewer (x y:Site n): exchangeF r p t c n x y=∑ i:Axis,∑ j:Axis, form t c j i* (transfer r p i n x (y+step j)-transfer r p i n x y):= by simp only [exchangeF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,ds_val]

variable (a b: G.ColorIndex)
lemma transfer_dye (x y:Cover): spend n x y (slope r p a) (columnA i b).x=if a=b then transfer r p i n (wrap n x) (wrap n y) else 0:= by
   rw [transfer_val i p r,descent]; simp_rw [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,column_d,smul_eq_mul]; by_cases he:a=b; subst b; simp only [mul_ite, mul_zero, and_true, ↓reduceIte,Finset.sum_ite_eq,Finset.mem_univ]; simp [ls]
   simp [Ne.symm he,he] -- test
lemma lead_x : diffA i j a = leadsL (step i) (columnA j a).x-(columnA j a).x:= by unfold diffA; rw [jetRow,jetRow,jetRow]; unfold columnA; simp only [leads_single, pointB,add_zero,zero_add]
lemma package (x y: Cover) : spend n x y (slope r p a) (slope t c b)= if a=b then exchangeF r p t c n (wrap n x) (wrap n y) else 0:= by
    nth_rw 1 [descent b t c]; simp_rw [skewer,map_sum,map_smul,lead_x,map_sub,spend_suby,transfer_dye]; by_cases h:a=b <;> simp [h]; rw [Finset.sum_comm]
def sprite (e:ℝ)(k:ℕ)(D:Scaff):Scaff:= ((e^(2+k))⁻¹) • D
def cutF (e:ℝ)(u v:Tops G): Scaff:= sprite e (u.k+v.k) (pathS u.x v.x)
def Wpp (e:ℝ)(r:ℝ)(p:Tet)(t:ℝ)(c:Tet): Scaff:= sprite e 2 (exchangeF r p t c)
def Wpv (e:ℝ)(r:ℝ)(p:Tet)(i:Axis): Scaff:= sprite e 1 (transfer r p i)
lemma paid_pv (x y:Cover)(e:ℝ):
   cutF e (upMark (spin r p a)) (columnA i b) n (wrap n x) (wrap n y)= if a=b then Wpv e r p i n (wrap n x) (wrap n y) else 0:= by
      unfold cutF upMark spin Wpv sprite; simp only [Pi.smul_apply,smul_eq_mul, path_eq,transfer_dye]; by_cases h:a=b <;> simp [h,columnA]
lemma paid_spin (x y:Cover)(e:ℝ):
   cutF e (upMark (spin r p a)) (upMark (spin t c b)) n (wrap n x) (wrap n y)= if a=b then Wpp e r p t c n (wrap n x) (wrap n y) else 0:= by
      unfold cutF upMark spin Wpp sprite; simp only [Pi.smul_apply,smul_eq_mul,path_eq, package]; by_cases h:a=b <;> simp [h]
-- exact corner
lemma feeK (u:Marks G)(v:Tops G) (x y: Cover){e:ℝ}(he:0<e): entryK n e x u y v= ↑(cutF e (upMark u) v n (wrap n x) (wrap n y)):= by rw [follow_r x y u v he]; unfold cutF sprite; simp only [Pi.smul_apply,smul_eq_mul,path_eq]; rw [inv_mul_eq_div]; rfl
-- probe-to-potential rows along vertex shift ∆ derivative normalized
lemma entryp_ce (x y:Cover){e:ℝ}(he:0<e): entryK n e x (spin r p a) y (columnA i b)= if a=b then ↑(Wpv e r p i n (wrap n x) (wrap n y)) else 0:= by rw [feeK _ _ _ _ he,paid_pv]; split_ifs <;> simp
lemma entrym_ce (x y:Cover){e:ℝ}(he:0<e): entryK n e x (spin r p a) y (upMark (spin t c b))= if a=b then ↑(Wpp e r p t c n (wrap n x) (wrap n y)) else 0:= by rw [feeK _ _ _ _ he,paid_spin]; split_ifs <;> simp
end YM.PositionX.Chir
