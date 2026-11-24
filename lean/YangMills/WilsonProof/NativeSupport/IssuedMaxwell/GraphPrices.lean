import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphGrade
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphPrices
open YM YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.FVA2.O.Score YM.FVA2.O.Project
open YangMills.MSbar IssuedMaxwell.Reports PowerSeries
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}
def entered (p:FLog g.core n):Ordinary.Price (B g) n:=
  fun w k t x=>∑b:Grade g.core w,coeff k (p t x (own b)) • vertex b
def posted (q:Ordinary.Price (B g) n):FLog g.core n:=
  fun t x b=>mk (fun k=>paygrade b.item (q b.h k t x))

theorem degree (p:FLog g.core n)(w k:ℕ)(t:ℝ)(x:Points n):
    Ordinary.homogeneous (B g) w (entered g p w k t x).val:=by
  apply (GraphGrade.original g _).mpr
  change YM.FVA2.Scale.Level.proj _ (∑b:Grade g.core w,coeff k (p t x (own b)) • vertex b)=_
  simp only [map_sum,map_smul,vertex_at]
  rfl

theorem paid (p:FLog g.core n):posted g (entered g p)=p:=by
  funext t x b
  rcases b with ⟨w,b⟩
  ext k
  change coeff k (mk _)=_
  rw [coeff_mk]
  change paygrade b (∑j:Grade g.core w,coeff k (p t x (own j)) • vertex j)=_
  rw [map_sum,Finset.sum_eq_single b]
  · rw [map_smul,pivotA,if_pos rfl,smul_eq_mul,mul_one]
  · intro j _ h
    rw [map_smul,pivotA,if_neg (Ne.symm h),smul_zero]
  · simp

theorem read (q:Ordinary.Price (B g) n)
    (grades:∀w k t x,Ordinary.homogeneous (B g) w (q w k t x).val):
    entered g (posted g q)=q:=by
  funext w k t x
  change (∑b:Grade g.core w,coeff k (mk _) • vertex b)=_
  simp only [coeff_mk]
  exact whole_grade _ ((GraphGrade.original g _).mp (grades w k t x))
end IssuedMaxwell.GraphPrices
end
