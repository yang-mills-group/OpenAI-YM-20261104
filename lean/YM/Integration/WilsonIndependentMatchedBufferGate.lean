import YM.Integration.WilsonPositionProgramTrialBufferedHome
/-! A single finite vacuum buffer, chosen by the first actual step reaching its joint bill. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedBufferGate
open Filter Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank.PathCost
open scoped BigOperators Classical
variable (S:Schedule)(K:ℕ)(w:ℝ)
def distance (w:ℝ):ℝ:=4*Real.log (1+|w|)
private theorem arrives:∃n:ℕ,K≤n ∧ S.scale K+distance w≤S.scale n:=
  ((eventually_ge_atTop K).and (S.divergent.eventually (eventually_ge_atTop _))).exists
def first:ℕ:=Nat.find (arrives S K w)
theorem purchased:K≤first S K w ∧ S.scale K+distance w≤S.scale (first S K w):=
  Nat.find_spec (arrives S K w)
theorem before {j:ℕ}(old:K≤j)(early:j<first S K w):S.scale j<S.scale K+distance w:=by
  by_contra! h
  exact (Nat.not_lt_of_ge (Nat.find_min' (arrives S K w) ⟨old,h⟩)) early
theorem overshoot:S.scale (first S K w)-S.scale K ≤
    distance w+(if first S K w=K then 0 else Real.log (S.block (first S K w-1)).val):=by
  split_ifs with atK
  · rw [atK,sub_self,add_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [abs_nonneg w]))
  · let n:=first S K w
    have holds:= (purchased S K w).1
    have lt:K<n:=by dsimp [n];omega
    have pred:n-1<n:=by omega
    have prev:= before S K w (j:=n-1) (by omega) pred
    have adj:(n-1)+1=n:=by omega
    have edge:=S.scale_succ (n-1)
    rw [adj] at edge
    change S.scale n - S.scale K≤distance w + Real.log (S.block (n-1)).val
    linarith
theorem fade (m:ℕ)(born:m≤K):
    trailC S m (first S K w)≤(1+|w|)⁻¹:=by
  have step:=(purchased S K w).2
  have lower:=scales S born
  have expBound:-(S.scale (first S K w)-S.scale m)/4≤ -Real.log (1+|w|):=by
    unfold distance at step
    linarith
  calc trailC S m (first S K w)≤Real.exp (-Real.log (1+|w|)):=Real.exp_le_exp.mpr expBound
       _=(1+|w|)⁻¹:=by rw [Real.exp_neg,Real.exp_log (by positivity)]

variable {T:Type*}[Fintype T](B ε:T→ℝ)
def demand:ℝ:=∑t,|B t|/ε t
theorem earned (positive:∀t,0<ε t)(m:ℕ)(born:m≤K)(t:T):
    B t*trailC S m (first S K (demand B ε))≤ε t:=by
  let w:=demand B ε
  have row t:0≤|B t|/ε t:=div_nonneg (abs_nonneg _) (positive t).le
  have bill:|B t|/ε t≤w:=Finset.single_le_sum (fun j _=>row j) (Finset.mem_univ t)
  have wpos:0<1+|w|:=by positivity
  have covers:|B t|≤ε t*(1+|w|):=by
    have h:|B t|/ε t≤1+|w|:=bill.trans (by linarith [le_abs_self w])
    have p:=(div_le_iff₀ (positive t)).mp h
    rwa [mul_comm] at p
  calc B t*trailC S m (first S K w)≤|B t| *trailC S m (first S K w):=
        mul_le_mul_of_nonneg_right (le_abs_self _) (trail_pos ..).le
       _ ≤ |B t| *(1+|w|)⁻¹:=mul_le_mul_of_nonneg_left (fade S K w m born) (abs_nonneg _)
       _ ≤ ε t:=by rw [←div_eq_mul_inv];exact (div_le_iff₀ wpos).2 covers

end YM.Integration.WilsonIndependentMatchedBufferGate
