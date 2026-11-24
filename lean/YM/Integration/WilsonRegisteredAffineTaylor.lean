import YM.Integration.WilsonRegisteredAffineDirection

/-! Taylor's theorem for an originally financed regular row about a
possibly nonflat starting configuration, along the actual left increment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAffineTaylor
open Function Set Finset Lattice Wilson RG Next.Rank.Spindle
open scoped Classical
variable {G:Gauge} {n:Side}

def jet (F:Config G n→ℂ) (W:Config G n) (v:Directions G n) (q:ℕ) (r:ℝ):ℂ :=
  ∑ j∈range (q+1),((j.factorial:ℝ)⁻¹*r^j) • leftDerivs F (List.replicate j v) W

private theorem observation (F:Config G n→ℂ) (W:Config G n) (v:Directions G n) (t:ℝ) (j:ℕ) :
    iteratedDeriv j (fun s=>F (increment W (s • v))) t=
      leftDerivs F (List.replicate j v) (increment W (t • v)) := by
  induction j generalizing t with
  | zero=>rfl
  | succ j ih=>
    rw [iteratedDeriv_succ,funext ih,List.replicate_succ,leftDerivs]
    let f:=fun s:ℝ=>leftDerivs F (List.replicate j v) (increment W (s • v))
    have same (s:ℝ):leftDerivs F (List.replicate j v) (increment (increment W (t • v)) (s • v))=f (t+s):=by rw [←progress]
    rw [funext same,deriv_comp_const_add,add_zero]

theorem original {p:BudgetPoint} {o:Site n} {Y:Support n} {F:Config G n→ℂ}
    (regular:p.Regular Y F) {c:ℝ} (funds:p.supBounds o Y F c) (W:Config G n)
    (v:Directions G n) (licensed:p.dirBound o v) {r:ℝ} (rp:0<r)
    (clean:∀ t∈Icc (0:ℝ) r,Healthy p.threshold Y (increment W (t • v)))
    (q:ℕ) (order:q+1 ≤ p.order) :
    ‖F (increment W (r • v))-jet F W v q r‖ ≤ c*r^(q+1)/q.factorial := by
  let h (s:ℝ):=F (increment W (s • v))
  let B:=Icc (0:ℝ) r
  have chart (t:ℝ) (ht:t∈B) (j:ℕ) (hj:j ≤ p.order):ContDiffAt ℝ j h t:=by
    let w:ℝ→Directions G n:=fun s=>(s-t) • v
    let g:Directions G n→ℂ:=F ∘ increment (increment W (t • v))
    have token:g ∘ w=h:=by
      funext s
      change F (increment (increment W (t • v)) ((s-t) • v))=F (increment W (s • v))
      rw [←progress,add_sub_cancel]
    rw [←token]
    apply ContDiffAt.comp _ _ (show ContDiffAt ℝ j w t by dsimp [w];fun_prop)
    change ContDiffAt ℝ j (F ∘ increment (increment W (t • v))) ((t-t) • v)
    rw [sub_self,zero_smul]
    exact (regular.smooth _ (clean t ht)).of_le (by exact_mod_cast hj)
  have valued (t:ℝ) (ht:t∈B) (j:ℕ) (hj:j ≤ p.order):‖iteratedDeriv j h t‖ ≤ c:=by
    rw [show iteratedDeriv j h t=_ from observation F W v t j]
    apply funds.2 _ (clean t ht) _ (by simpa using hj)
    intro w hw
    exact (List.eq_of_mem_replicate hw) ▸ licensed
  have unique (t:ℝ) (ht:t∈B) (j:ℕ) (hj:j ≤ p.order):iteratedDerivWithin j h B t=iteratedDeriv j h t:=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc rp) (chart t ht j hj) ht
  have bound:=taylor_mean_remainder_bound (n:=q) (f:=h) rp.le
    (fun t ht=>ContDiffWithinAt.of_le (chart t ht (q+1) order).contDiffWithinAt (by simp))
    (right_mem_Icc.mpr rp.le) (C:=c) (fun t ht=>by rw [unique t ht (q+1) order];exact valued t ht _ order)
  have base:increment W ((0:ℝ) • v)=W:=by ext1 e;simp [increment]
  have atZero:0∈B:=left_mem_Icc.mpr rp.le
  have same: taylorWithinEval h q B 0 r=jet F W v q r:=by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro j hj
    rw [sub_zero,unique 0 atZero j ((Nat.le_of_lt (mem_range.mp hj)).trans order),
      show iteratedDeriv j h 0=_ from observation F W v 0 j,base]
  rw [sub_zero,same] at bound
  exact bound

end YM.Integration.WilsonRegisteredAffineTaylor
end
