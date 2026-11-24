import YM.SchemeConversionRG11.FirstMS.Triad.Against

/-! The actual V1 with all three assignments to distinct marks. Cyclic color factor factored
out (oriented z,x,y). -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

def slide (i:P):P:= i+1
def lag (i:P):P:= i-1

section
attribute [-instance] Classical.propDecidable
lemma circles : ∀ j,slide (slide j)=lag j:=by decide
lemma loops_back : ∀ j,slide (lag j)=j:=by decide
lemma loops_second : ∀ j,lag (slide j)=j:=by decide
lemma neg1 : ∀ j,slide j≠j:=by decide
lemma neg2 : ∀ j,lag j≠j:=by decide
lemma neg3 : ∀ j,lag j≠slide j:=by decide
lemma full_order : ∀ j i,i=j∨i=slide j∨i=lag j:=by decide
end

def orderP (j:P)(b c d:Axis)(k:P):Axis:= if k=j then b else if k=slide j then c else d
@[simp] lemma fore (j:P)(b c d: Axis): orderP j b c d j=b:= by simp [orderP]
@[simp] lemma stern (j:P)(b c d:Axis): orderP j b c d (slide j)=c:= by simp [orderP,neg1]
@[simp] lemma abaft (j:P)(b c d: Axis): orderP j b c d (lag j)=d:=by simp [orderP,neg2,neg3]
lemma shift_load (j:P)(b c d:Axis): orderP (slide j) c d b=orderP j b c d:= by
    ext k; rcases full_order (slide j) k with hh|hh|hh <;> rw [hh]
    · rw [fore,stern];
    · rw [stern,circles,abaft]
    rw [abaft,loops_second,fore]
lemma flood_load (j:P): (Finset.univ.erase j)={slide j,lag j}:=by
   ext i
   suffices i≠j ↔ i=slide j∨i=lag j by simpa
   exact ⟨fun hh=>(full_order j i).resolve_left hh, fun hi=>hi.elim (fun hh ht=>neg1 j (hh.symm.trans ht)) (fun hh ht=>neg2 j (hh.symm.trans ht))⟩

-- σ(dual)=exact in chosen mark. major, ε eps.
variable {x:Nodes}{R ρ:ℝ}
def glow (j:P): Bool:= decide (j=0)

def stove (w:P→Fin 3)(α:P→Axis)(j:P):Stem:= ⟨j,glow j,w j,α j⟩

variable (h:Box x R ρ) (w:P→Fin 3)

/-- ∂ axis a, component b, then A_c, A_d in cyclic order. Tensor enforces V
 intended full d action on physical components; minus sign from exchanging the last two vertex
 slots through colorF. Distinct only. -/
def mainPair (a b c d:Axis):ℂ:= ((if a=c ∧ b=d then 1 else 0) - (if a=d ∧ b=c then 1 else 0):ℤ)
def prime (x:Nodes)(R ρ:ℝ)(j:P)(b c d a:Axis):ℂ→ℂ:= multiplies (stove w (orderP j b c d)) j a x R ρ
def pass (x:Nodes)(R ρ:ℝ)(j:P)(K:Axis→Axis→Axis→Axis→ℂ)(z:ℂ):ℂ := ∑ a,∑ b,∑ c,∑ d,K a b c d*prime w x R ρ j b c d a z

def stemTensor (p:Bool)(a b c d:Axis):ℂ:= 2⁻¹*(↑(tension p a b c d):ℂ)

lemma main_tensor (a b c d:Axis):
    mainPair a b c d= 2*stemTensor false a b c d- (2:ℂ)⁻¹*(skew a b c d):= by
    have hk:=complete a b c d
    unfold mainPair skew stemTensor
    have he:= congrArg ((↑):ℤ→ℂ) hk
    simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_sub] at he ⊢; linear_combination -he/2

include h

lemma bows : (∑ j:P, pass w x R ρ j (fun a b c d=>skew a b c d) 0)=0:=by
   -- collect coefficients reindexed in Mark order. twists align
   let H(j:P)(a b c d:Axis):ℂ:= ↑(skew a b c d)*multiplies (stove w (orderP 0 b c d)) j a x R ρ 0
   have ht(i j:P): (∑ a,∑ b,∑ c,∑ d,(skew a b c d:ℂ)* multiplies (stove w (orderP (slide i) b c d)) j a x R ρ 0) =
       ∑ a,∑ b,∑ c,∑ d,(skew a b c d:ℂ)*multiplies (stove w (orderP i b c d)) j a x R ρ 0 := by
       refine Finset.sum_congr rfl fun a _=>?_
       conv_lhs =>
          enter [2,b]; rw [Finset.sum_comm]
       rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
       refine Finset.sum_congr rfl fun c _=> Finset.sum_congr rfl fun d _=> by rw [turns a c d b, shift_load]
   have he(j:P): pass w x R ρ j (fun a b c d=>↑(skew a b c d)) 0= ∑ a,∑ b,∑ c,∑ d,H j a b c d:= by
       unfold pass prime H
       rcases full_order 0 j with he|he|he
       · rw [he]
       · rw [he,ht]
       rw [he,← circles, ht,ht]
   simp_rw [he]; rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro a _
   rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro b _
   rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro c _
   rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun d _=> ?_
   simp only [H,← Finset.mul_sum,charge_erases h (stove w _) a (fun _=>rfl),mul_zero]

lemma port_anti : ∑ j:P,pass w x R ρ j mainPair 0=∑ j:P,2*pass w x R ρ j (stemTensor false) 0:=by
    have he(j:P): pass w x R ρ j mainPair 0= 2*pass w x R ρ j (stemTensor false) 0 - 2⁻¹*pass w x R ρ j (fun a b c d=>skew a b c d) 0:= by
       simp only [pass,main_tensor,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
    simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum, bows h w, mul_zero,sub_zero]

omit h

lemma load_spark (j:P)(b c d e:Axis): incline j (stove w (orderP j b c d)) e = stove w (orderP j e c d):= by
   funext k; rcases eq_or_ne k j with rfl|hk
   · simp only [incline,update_self]; simp [stove,fore]
   simp [incline,hk,stove, orderP]

def fair (x:Nodes)(R ρ:ℝ)(j:P)(m:Fin 3):ℂ:= ∑ c:Axis,∑ d:Axis,(fan false m c d:ℂ)*spark_at (stove w (orderP j 0 c d)) j false m x R ρ
lemma collect {x:Nodes}(R ρ:ℝ)(j:P): pass w x R ρ j (stemTensor false) 0=∑ m:Fin 3, fair w x R ρ j m:=by
    simp only [pass,fair,spark_at,load_spark,prime,stemTensor,← valve,Finset.mul_sum,Finset.sum_mul]
    conv_lhs =>
       enter [2,a,2,b,2,c]
       rw [Finset.sum_comm]
    conv_lhs =>
       enter [2,a,2,b]
       rw [Finset.sum_comm]
    conv_lhs =>
       enter [2,a]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro m _
    conv_lhs =>
       enter [2,a]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _=>?_
    conv_lhs=> enter [2,a]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun d _=> Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> by ring

end YM.SchemeConversionRG11.FirstMS.Triad
