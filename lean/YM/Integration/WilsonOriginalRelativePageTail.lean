import YM.Integration.WilsonOriginalConnectedPeriodPage

/-! After fixing the copy of a connected root, the other occupied source centers
still range over their own full-period fibers. A term with a different lift uses
the length of a path in that same connected component. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalRelativePageTail
open Lattice Finset Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open scoped BigOperators Classical
variable {n N:Side} {ι X:Type*}

def retained (h:n.val∣N.val) (site:ι→Site N) (i:ι):Fin (Pages n N):=
  (page h (splitter h (site i))).symm ⟨site i,(posted _ _ _).mpr rfl⟩

def locate (h:n.val∣N.val) (site:ι→Site N) (p:ι→Fin (Pages n N)) (i:ι):Site N:=
  (page h (splitter h (site i)) (p i)).val

theorem chosen (h:n.val∣N.val) (site:ι→Site N) (i:ι):
    locate h site (retained h site) i=site i:=by
  unfold retained locate
  rw [Equiv.apply_symm_apply]

private theorem span_gap (h:n.val∣N.val) (root:Site N) (site:ι→Site N) (D:ℝ)
    (near:∀i,(separation root (site i):ℝ) ≤ D) (p:ι→Fin (Pages n N))
    (different:p≠retained h site) {A:ℝ}
    (paths:∀i,(separation root (locate h site p i):ℝ) ≤ A): (n.val:ℝ) ≤ A+D:=by
  obtain ⟨i,failed⟩:∃i,p i≠retained h site i:=by
    by_contra! same
    exact different (funext same)
  let y:=page h (splitter h (site i)) (p i)
  have referred:splitter h y.val=splitter h (site i):=(posted ..).mp y.prop
  have missed:y.val≠site i:=by
    intro equal
    apply failed
    apply (page h (splitter h (site i))).injective
    apply Subtype.ext
    change y.val=locate h site (retained h site) i
    rw [chosen,equal]
  have gap: n.val ≤ separation y.val (site i):=(blocks_at_floor h).apart _ _ referred missed
  have trip:=gap.trans (separation_triangle y.val root (site i))
  rw [separation_comm y.val root] at trip
  have trip':(n.val:ℝ) ≤ (separation root (locate h site p i):ℝ)+(separation root (site i):ℝ):=by exact_mod_cast trip
  exact trip'.trans (add_le_add (paths i) (near i))

theorem original [Fintype ι] [Fintype X] (h:n.val∣N.val) (root:Site N) (site:ι→Site N)
    (K:(ι→Fin (Pages n N))→X→ℂ) (span:(ι→Fin (Pages n N))→X→ℝ) (output:X→ℝ)
    {ρ D d M:ℝ} (positive:0 ≤ ρ) (near:∀i,(separation root (site i):ℝ) ≤ D)
    (connected:∀p x i,(separation root (locate h site p i):ℝ) ≤ span p x)
    (charged:∀p x,output x ≤ span p x+d)
    (paid:(∑p,∑x,Real.exp (ρ*span p x)*‖K p x‖) ≤ M) :
    (∑x,Real.exp (ρ*output x/2)*‖(∑p,K p x)-K (retained h site) x‖) ≤
      Real.exp (-(ρ*(n.val-D-d))/2)*M:=by
  let keep:=retained h site
  let others:Finset (ι→Fin (Pages n N)):=univ.erase keep
  let fee:=Real.exp (-(ρ*(n.val-D-d))/2)
  have split (x:X):(∑p,K p x)-K keep x=∑p∈others,K p x:=by
    apply sub_eq_of_eq_add
    exact (sum_erase_add _ _ (mem_univ keep)).symm
  have rate (p) (bad:p∈others) (x:X):
      Real.exp (ρ*output x/2) ≤ fee*Real.exp (ρ*span p x):=by
    have reach:=span_gap h root site D near p (mem_erase.mp bad).1 (connected p x)
    have one:=charged p x
    dsimp only [fee]
    rw [←Real.exp_add,Real.exp_le_exp]
    nlinarith only [mul_nonneg positive (sub_nonneg.mpr reach),mul_nonneg positive (sub_nonneg.mpr one)]
  have raised (x:X):
      Real.exp (ρ*output x/2)*‖(∑p,K p x)-K keep x‖ ≤
        fee * ∑p∈others,Real.exp (ρ*span p x)*‖K p x‖:=calc
    _ ≤ Real.exp (ρ*output x/2)*(∑p∈others,‖K p x‖):=by
      rw [split];exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (Real.exp_pos _).le
    _ ≤ _ :=by
      rw [mul_sum,mul_sum]
      apply sum_le_sum
      intro p hp
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (rate p hp x) (norm_nonneg _)
  calc
    _ ≤ ∑x,fee*(∑p∈others,Real.exp (ρ*span p x)*‖K p x‖):=sum_le_sum fun x _=>raised x
    _ = fee*(∑p∈others,∑x,Real.exp (ρ*span p x)*‖K p x‖):=by rw [←mul_sum,sum_comm]
    _ ≤ _ :=by
      exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _=>sum_nonneg fun x _=>
        mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).trans paid) (Real.exp_pos _).le

end YM.Integration.WilsonOriginalRelativePageTail
