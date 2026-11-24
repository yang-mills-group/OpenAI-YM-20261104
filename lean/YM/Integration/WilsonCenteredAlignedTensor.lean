import YM.Integration.WilsonCenteredAlignedStencil

/-! Bounded signed interpolation on all actual shape coordinates. The number
of aligned probes at fixed radius does not enter the nodal price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredAlignedTensor
open Function Filter Set Finset OPE.PolyDisk OPE.Stencils
open scoped Classical BigOperators
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem original (n:ℕ) :
    ∃ C:ℝ,1≤C ∧ ∀ (a δ B:ℝ),0<a → 0≤δ → 0≤B →
      ∀ (p:ι→ℝ) (f:(ι→ℝ)→ℂ),
      (∀ y,valid (n+1) a (univ:Finset ι).toList p y → ‖f y‖≤δ) →
      (∀ x i,Partway (n+1) a [i] p x →
        let h:=a*((n+1:ℕ)+3)
        let I:=Icc (0:ℝ) h
        let D:=fun t:ℝ=>f (update x i (x i+t))
        ContDiffOn ℝ (n+1) D I ∧ ∀ y∈I,‖iteratedDerivWithin (n+1) D I y‖≤B) →
      ‖f p‖≤C*(δ+B*a^(n+1)) :=by
  obtain ⟨K,k1,pay⟩:=WilsonCenteredAlignedStencil.original n
  obtain ⟨R,r1,weights⟩:=lag_budget (n+1)
  let M:=Fintype.card ι
  let C:=K*(1+R)^M
  have rr : 1≤1+R:=by linarith only [r1]
  have c1:1≤C:=one_le_mul_of_one_le_of_one_le k1 (one_le_pow₀ rr)
  refine ⟨C,c1,?_⟩
  intro a δ B ap dp bp p f small controlled
  let run:=(univ:Finset ι).toList
  have nodup:run.Nodup:=Finset.nodup_toList _
  have len:run.length=M:=by simp [run,M]
  have tariff (p:ℝ): (∑ j:Fin (n+1),‖lagWeight (angle a p) j‖)≤R:=weights _ (angle_law a)
  have nodes:=tensor_bound (n+1) a tariff dp run nodup p f small
  have oneStep (x:ι→ℝ) (i:ι) (hx:Partway (n+1) a [i] p x) (_:i∈(univ:Finset ι)) :
      ‖f x-tensor (n+1) a x f [i]‖≤K*B*a^(n+1):=by
    obtain ⟨smooth,bound⟩:=controlled x i hx
    have hr:=pay a (x i) B ap bp (fun t=>f (update x i (x i+t))) smooth bound
    simpa only [add_zero,update_eq_self,tensor,smul_eq_mul,step_affine (n+1) a ap] using hr
  have initial:Partway (n+1) a run p p:=fun i=>⟨fun _=>rfl,fun j _=>by
    rw [sub_self];exact ⟨le_rfl,mul_nonneg ap.le (by positivity)⟩⟩
  have bx:0≤K*B*a^(n+1):=mul_nonneg (mul_nonneg (zero_le_one.trans k1) bp) (pow_nonneg ap.le _)
  have total:=tensorCost (n+1) a tariff bx ap oneStep p run nodup initial (fun _ _=>mem_univ _)
  rw [len] at nodes total
  have rc:R^M≤C:=calc
    _ ≤(1+R)^M:=pow_le_pow_left₀ (zero_le_one.trans r1) (by linarith only [r1]) _
    _ ≤C:=le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans rr) _) k1
  calc
    _ ≤ ‖f p-tensor (n+1) a p f run‖+‖tensor (n+1) a p f run‖ :=(norm_le_insert' _ _).trans_eq (add_comm _ _)
    _ ≤ K*B*a^(n+1)*(1+R)^M+δ*R^M:=add_le_add total nodes
    _ ≤ K*B*a^(n+1)*(1+R)^M+δ*C:=add_le_add_right (mul_le_mul_of_nonneg_left rc dp) _
    _ = _:=by dsimp [C];ring

end YM.Integration.WilsonCenteredAlignedTensor
