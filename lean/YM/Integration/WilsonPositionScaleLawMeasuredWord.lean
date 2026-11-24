import YM.Integration.WilsonPositionScaleLawMeasuredSection

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredWord
open Finset Function Filter Set PowerSeries Maxwell XSpace XSpace.Normalize
open scoped BigOperators Classical Topology
variable {G:Gauge}{d n:ℕ}
abbrev Word (n q:ℕ) := Option (Fin n)→Fin (q+1)
def weight {q:ℕ} (w:Word n q) : ℕ := ∑i,(w i).val
def node (T:Guard G d)(R:Reports G d)(φ:Test n)(v:Fin n→Sec G d){q:ℕ}(w:Word n q) : ℂ :=
  R (w none).val n φ (fun i=>coeff (w (some i)).val T (v i))

theorem atOrder (T:Guard G d)(R:Reports G d)(φ:Test n)(v:Fin n→Sec G d){q l:ℕ}(room:l≤q) :
    realm T R l n φ v=∑w:Word n q,if weight w=l then node T R φ v w else 0 :=by
  rw [really,←Finset.sum_filter]
  let book (a:Days n)(ha:a∈tally l n) : Word n q :=fun i=>⟨a i,by
    have total:∑j,a j=l:=(totaled a).1 ha
    have part:a i≤∑j,a j:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    omega⟩
  apply Finset.sum_bij (fun a ha=>book a ha)
  · intro a ha
    exact mem_filter.mpr ⟨mem_univ _,(totaled a).mp ha⟩
  · intro a ha b hb e
    ext i
    exact congrArg (fun w:Word n q=>(w i).val) e
  · intro w hw
    let a:Days n:=Finsupp.equivFunOnFinite.symm (fun i=>(w i).val)
    have val (i:Option (Fin n)):a i=(w i).val:=by simp [a]
    have ha:a∈tally l n:=(totaled a).2 (by simpa only [val,weight] using (mem_filter.mp hw).2)
    refine ⟨a,ha,?_⟩
    funext i
    exact Fin.ext (val i)
  · intro a ha
    rfl

def clipped (T:Guard G d)(R:Reports G d)(q:ℕ)(u:ℝ)(φ:Test n)(v:Fin n→Sec G d) : ℂ :=
  ∑l∈range (q+1),(u:ℂ)^l * realm T R l n φ v

def opened (T:Guard G d)(R:Reports G d)(q:ℕ)(u:ℝ)(φ:Test n)(v:Fin n→Sec G d) : ℂ :=
  ∑w:Word n q,(u:ℂ)^(weight w) * node T R φ v w

theorem selected (T:Guard G d)(R:Reports G d)(q:ℕ)(u:ℝ)(φ:Test n)(v:Fin n→Sec G d) :
    clipped T R q u φ v=∑w:Word n q,if weight w≤q then (u:ℂ)^(weight w)*node T R φ v w else 0 :=by
  unfold clipped
  calc
    _=∑l∈range (q+1),∑w:Word n q,if weight w=l then (u:ℂ)^l*node T R φ v w else 0 :=by
      apply sum_congr rfl
      intro l hl
      rw [atOrder T R φ v (Nat.le_of_lt_succ (mem_range.mp hl)),mul_sum]
      apply sum_congr rfl
      intro w _
      split_ifs <;> simp_all
    _=∑w:Word n q,∑l∈range (q+1),if weight w=l then (u:ℂ)^l*node T R φ v w else 0 :=sum_comm
    _=_:=by simp

theorem error (T:Guard G d)(R:Reports G d)(q:ℕ)(u:ℝ)(small:|u|≤1)(φ:Test n)(v:Fin n→Sec G d) :
    ‖opened T R q u φ v-clipped T R q u φ v‖≤|u|^(q+1)*∑w:Word n q,‖node T R φ v w‖ :=by
  rw [opened,selected,←sum_sub_distrib,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro w _
  by_cases h:weight w≤q
  · simp only [if_pos h,sub_self,norm_zero]
    positivity
  · rw [if_neg h,sub_zero,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg u) small (show q+1≤weight w by omega)) (norm_nonneg _)

end YM.Integration.WilsonPositionScaleLawMeasuredWord
