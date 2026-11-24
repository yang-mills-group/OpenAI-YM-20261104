import YM.RG12.Alidade.Stencil
/-! # The strict shear selected by low-order comparison, and stability of certified steps -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Finset Frames Real
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Grade d→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)][FiniteDimensional ℂ (Col V)] {F:Type}[AddCommGroup F][Module ℂ F]

structure strict (A : Form (V:=Col V)) : Prop where
    plane : triangular V A
    units i (v:V i) : block V A i i v = 0
set_option quotPrecheck false
local notation "Knot"=> Col V
lemma remains (M:Mixes (V:=Knot))(T:Charge (V:=Knot))(t s:ℝ)(hm:0 ≤ t)(h:s*(t+t^2) ≤1/2)(hS:Casket T M s)(he:strict M.first)(hf:strict M.second):
    ∃ J:MC V, (∀ x, turned M t (J x)=x)∧ triangular V J.toLinearMap ∧ (∀ i,∀x : V i,block V J.toLinearMap i i x=x) ∧
    ∀ x, ‖J x‖ ≤ 2*‖x‖ ∧ ‖J.symm x‖ ≤ 2*‖x‖:=by
    let A:=turned M t
    have hv : ∀ x, ‖A x-x‖ ≤ 1/2*‖x‖:=fun x=>(corner T M x hS hm).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))
    have he' x : ‖x‖ ≤ 2*‖A x‖:=by
       have hh : ‖x‖ ≤ ‖A x-x‖+‖A x‖:=by
          nth_rw 1 [show x=A x-(A x-x) from by abel]
          exact (norm_sub_le ..).trans_eq (add_comm ..)
       linarith only [hv x,hh]
    have hA:Bijective A:=by
       have h :Injective A:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx=> by
           have hh:=he' x; rw [hx,norm_zero,mul_zero] at hh; exact norm_le_zero_iff.mp hh)
       exact ⟨h,LinearMap.surjective_of_injective h⟩
    let K:=(LinearEquiv.ofBijective A hA)
    have hT: triangular V K.toLinearMap:=by
       intro i j hij x; change A _ _ = _
       unfold A turned; simp only [LinearMap.add_apply, LinearMap.id_coe, LinearMap.smul_apply,Pi.add_apply,Pi.smul_apply, id_eq]
       change put V j x i + _+_= _; have hi': (M.first (put V j x)) i=0:=he.plane i j hij _; have hj':(M.second (put V j x)) i=0 :=hf.plane i j hij _
       rw [hi',hj']; simp [put,ne_of_gt hij]
    have hD i (x:V i): block V K.toLinearMap i i x=x:=by
       change A _ _= _; unfold A turned; simp only [LinearMap.add_apply, LinearMap.smul_apply,LinearMap.id_coe,id_eq,Pi.add_apply, Pi.smul_apply]
       rw [show (M.first (put V i x)) i=0 from he.units i x,
           show (M.second (put V i x)) i=0 from hf.units i x]; simp [put]
    refine ⟨K.symm,K.apply_symm_apply,hT.inv,fun i x=> ?_, fun x=> ?_⟩
    · exact (hD i _).symm.trans (inv_diag hT i x)
    constructor
    · refine (he' _).trans_eq ?_
      rw [show A _=x from K.apply_symm_apply x]
    change ‖A x‖ ≤ _
    have he : ‖A x‖ ≤ ‖A x-x‖+‖x‖:=by
       conv_lhs=>rw [show A x=A x-x+x from by abel]
       exact norm_add_le ..
    linarith only [he,hv x,norm_nonneg x]

/-- Lens pair amplitude stability, using just second-order relevance and two-point quadratic
positivity on moving calibrated pivots. Allows universal constant in front of the calendar
increment, prices after sqrt and coercivity. -/
theorem permits {s s' r A K g g':ℝ}{m:ℕ}{v:ℝ}(h :0≤g) (_ht:0≤v) (hK:v^2 ≤ K*g) (hA:0 ≤ A)(hg:|g'-g|≤ A*r*v^2)
    (hr:0 ≤ r)(hs:1+r ≤ s'/s)(hn:K*A ≤ m)(hi:2*K*A*r ≤ 1):
    Real.sqrt g' ≤ (s'/s)^(2*m)*Real.sqrt g ∧ Real.sqrt g ≤ (s'/s)^(2*m)*Real.sqrt g':=by
    let u:=K*A*r
    have hp:1 ≤ s'/s:= (by linarith only [hs,hr])
    rcases lt_or_ge K 0 with hv|hv
    · have he: v^2=0:=le_antisymm (hK.trans (mul_nonpos_of_nonpos_of_nonneg hv.le h)) (sq_nonneg _)
      rw [he,mul_zero] at hg; rw [sub_eq_zero.mp (abs_nonpos_iff.mp hg)]; constructor <;> exact le_mul_of_one_le_left (Real.sqrt_nonneg _) (one_le_pow₀ hp)
    have hu:0 ≤ u:=by unfold u; positivity
    have hh : (1-u)*g ≤ g' ∧ g' ≤ (1+u)*g:=by
       obtain ⟨hl,hk⟩:=abs_le.mp hg; unfold u; constructor<;>nlinarith only [hl,hk,mul_le_mul_of_nonneg_left hK (mul_nonneg hA hr)]
    have ht₀:(1-u) ≥ 0:=by unfold u; linarith only [hi]
    have hg': 0 ≤ g':=(mul_nonneg ht₀ h).trans hh.1
    have he:1 ≤ (1+2*u)*(1-u):=by
      have he': 1-2*u ≥ 0:=by unfold u;linarith only [hi]
      nlinarith only [mul_nonneg hu he']
    have hL : 1+2*u ≤ (s'/s)^(2*m):=by
       have ht:= mul_le_mul_of_nonneg_right hn hr
       have hu:=one_add_mul_le_pow (a:=r) (by linarith only [hr] : (-2:ℝ) ≤ r) (2*m)
       push_cast at hu
       apply le_trans _ (pow_le_pow_left₀ (by positivity : 0 ≤ 1+r) hs (2*m))
       unfold u; linarith only [hu,ht]
    let L:= (s'/s)^(2*m); have hf:1≤L:=one_le_pow₀ hp
    have hW {x y:ℝ}(hx:0≤x)(hy:0≤y)(ht:x ≤ (1+2*u)*y):Real.sqrt x ≤ L*Real.sqrt y:=by
       apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (mul_nonneg (zero_le_one.trans hf) (Real.sqrt_nonneg _)); rw [Real.sq_sqrt hx,mul_pow,Real.sq_sqrt hy]; exact ht.trans (mul_le_mul_of_nonneg_right (hL.trans (le_self_pow₀ hf (by decide))) hy)
    refine ⟨hW hg' h (hh.2.trans (mul_le_mul_of_nonneg_right ?_ h)),hW h hg' ?_⟩
    · linarith only [hu]
    calc g ≤ (1+2*u)*(1-u)*g:= le_mul_of_one_le_left h he
         _ ≤ (1+2*u)*g':=by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hh.1 (by positivity)
end YM.RG12.Alidade
