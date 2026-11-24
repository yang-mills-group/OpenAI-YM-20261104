import YM.OPE.Compatible.Ash.Pine
/-! # Oversampled shear estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {n:Side}{t c s:ℝ}{r j v: ℕ}{D:List Axis}
private lemma sail (f:E4→ℂ)(hf:∀ x,2 ≤ ‖x‖→ f x=0)
    (ht:0<t)(ht':t ≤ 1)(hm:mesh n*v ≤1/2) (p:Site n)(g:Axis):
    let e:=((-t⁻¹)*mesh n) • basis g
    gridDiff (-step g) v (f ∘ stretch t) p=punch e v f (stretch t p):=by
   refine translated v ?_; intro j hj; let a:=Lattice.lift p -j • step g
   rw [path_ordinal t g p j, smul_neg, ←sub_eq_add_neg]; let y:=p-j • step g; let x:=t⁻¹ • incVec (mesh n) a; change f (stretch t y)= f x
   by_cases he:a=Lattice.lift y
   · unfold x; rw [he]; rfl
   have hu: wrap n a=y:=by simp only [a,map_nsmul,map_sub, wrap_lift,wrap_step]; rfl
   have hb:= spill_near (le_trans hm (show (1:ℝ)/2 ≤ Real.pi-2 from by linarith [Real.pi_gt_three])) hj p g he; have hc:=Pert.Band.spill (j:=0) (v:=x) (f:=g) a (show _ by rwa [hu])
   rw [hf _ (by rw [stretch_norm ht,le_div_iff₀ ht]; linarith only [hb,ht']), hf x (by dsimp only [x]; rw [norm_smul,norm_inv,Real.norm_of_nonneg ht.le,inv_mul_eq_div,le_div_iff₀ ht];linarith only [Real.pi_gt_three,hc,ht'])]
private lemma safer (f:E4→ℂ)(hf:∀ x,2 ≤ ‖x‖→ f x=0)(h: Smooth v (closedBall (0:E4) 6) f) (hg:∀ x∈closedBall (0:E4) 6,‖iteratedFDeriv ℝ v f x‖≤c)
    (ht:0<t)(ht': t≤1)(hm:mesh n*v ≤ 1/2)(hv:mesh n*v ≤ t)(p:Site n) (i:Axis): let T:=mesh n/t
    ‖gridDiff (-step i) v (f ∘ stretch t) p‖ ≤ if ‖stretch t p‖ ≤ 3 then T^v*c else 0:=by
   intro T; rw [sail f hf ht ht' hm]; let e:=(-t⁻¹*mesh n) • basis i; have he:‖e‖=T:=by unfold e T; rw [norm_smul, neg_mul,Real.norm_eq_abs,abs_neg,abs_of_pos (mul_pos (inv_pos.mpr ht) mesh_pos),basis_norm,mul_one,inv_mul_eq_div]
   have hg' : (v:ℝ)*T ≤ 1:=by unfold T; rw [← mul_div_assoc,div_le_iff₀ ht,mul_comm,one_mul]; exact hv
   have hh(j:ℕ)(hj:j<v):‖(j+1) • e‖ ≤ 1:=by rw [← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_natCast,he]; apply le_trans _ hg'; exact mul_le_mul_of_nonneg_right (show ((j+1:ℕ):ℝ)≤ v by exact_mod_cast hj) (by rw [←he]; positivity)
   rw [←he]
   split_ifs with hi
   · refine puncture _ (closedBall (0:E4) 6) (convex_closedBall (0:E4) 6) (stretch t p) e c _ ⟨by rw [mem_closedBall,dist_zero_right]; linarith only [hi],?_⟩ h hg; intro j hj; rw [mem_closedBall,dist_zero_right,add_assoc,← succ_nsmul]; grw [norm_add_le,hh j hj]; linarith only [hi]
   rw [punch_far (not_le.mp hi) (e:=e) v (by rw [he]; exact hg') _ hf]; simp
lemma shelled (f:E4→ℂ)(hf:∀ x,2 ≤ ‖x‖→ f x=0)(h: Smooth v (closedBall (0:E4) 6) f) (hg:∀ x∈closedBall (0:E4) 6,‖iteratedFDeriv ℝ v f x‖≤c)(hc:0≤c)
    (ht:0<t)(ht':t ≤1)(hm:mesh n*v ≤1/2)(hv:mesh n*(v+1)≤t)(i:Axis)(z:Site n): let T:=mesh n / t
    ‖char (step i) z-1‖^v * ‖∑ p,char p z * f (stretch t p)‖ ≤ 8^4*c/(T^4)*T^v:=by
   intro T; rw [←Complex.norm_pow,←Complex.norm_mul]; change ‖(char (step i) z-1)^v * ∑ p,char p z*(f ∘ stretch t) p‖ ≤ _
   rw [← sum_punch]; apply (norm_sum_le ..).trans
   have hp :=mesh_pos (n:=n); have hy:=safer f hf h hg ht ht' hm (by linarith only [hv,hp])
   have he := near_count ht (n:=n) (by rw [le_div_iff₀ hp]; have hx : (v:ℝ) ≥ 0:=Nat.cast_nonneg _; nlinarith only [hx,hp,hv]); dsimp only at he
   grw [show (∑ p:Site n, ‖char p z*gridDiff (-step i) v (f ∘ stretch t) p‖) ≤ ∑ p∈ Finset.univ.filter (fun p:Site n=>‖stretch t p‖≤3),T^v*c by rw [Finset.sum_filter]; apply Finset.sum_le_sum; intro p _; rw [Complex.norm_mul,norm_char,one_mul]; exact hy p i]; rw [Finset.sum_const,nsmul_eq_mul]
   exact (mul_le_mul_of_nonneg_right he (by unfold T; positivity)).trans (le_of_eq (by unfold T; field_simp))
lemma vet_bank (hs:1 ≤ s)(D:List Axis)(a:Cover)(r v:ℕ):
 let g(t:ℝ)(x:E4):=Pert.Band.middle D t x * Complex.exp ((corner a (t • x):ℝ)*Complex.I)
 ∃ C≥0,∀ (n:Side)(t:ℝ),0<t→ t≤1→mesh n*v≤1/2→mesh n*(v+1)≤t→∀ i z,
   let T:=mesh n/t
   ‖char (step i) z-1‖^v * ‖∑ p:Site n,char p z * vet s r g t (stretch t p)‖ ≤ C*t^r/(T^4)*T^v:=by
   intro g; have H(x:ℝ)(hx:x∈ Icc 0 1)(z:E4): ContDiffAt ℝ ∞ (Function.uncurry g) (x,z):=by
       apply (middle_diff D x (show |x|≤ 1 by rw [abs_of_nonneg hx.1]; exact hx.2) z).mul (f:=Function.uncurry (middle D)) (g:=fun a':ℝ×E4=> Complex.exp ((corner a (a'.1 • a'.2):ℝ)*Complex.I)); unfold Pert.Full.corner; apply ContDiffAt.cexp; refine ContDiffAt.mul (g:=fun _:ℝ × E4=> Complex.I) ?_ contDiffAt_const; apply Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=fun a':ℝ×E4=> corner a (a'.1 • a'.2)); unfold Pert.Full.corner; fun_prop
   obtain ⟨C,hC,hv⟩:= vet_price hs (isCompact_closedBall (0:E4) 6) v r H; refine ⟨8^4*C,by positivity,fun n t ht ht' hm hh i z=>?_⟩; intro T
   have hx:Smooth v (closedBall (0:E4) 6) (vet s r g t):=fun x _=> (vet_silk (t:=1) hs (fun u hu=>H u hu x) ⟨ht.le,ht'⟩).of_le (by norm_cast; simp)
   have hf(x:E4)(hh:2 ≤ ‖x‖): vet s r g t x=0:=by
      have hy(k j)(hj:j=k):∀ t x', x'=x → vet s k g t x'=0:=by
         subst j; induction k with
         | zero=> rintro v m hhv; subst m; change g v x=0; dsimp only [g,middle]; simp only [outermost hh,disk_out (le_trans one_le_two hh),sub_self,Complex.ofReal_zero,zero_mul]
         | succ k ih=> rintro v m h;change vet s k g v m-s^k • vet s k g (v/s) m=0; rw [ih _ _ h, ih _ _ h];simp
      exact hy _ _ rfl _ _ rfl
   apply (shelled _ hf hx (fun x hz=> hv x hz t ⟨ht.le,ht'⟩) (by positivity) ht ht' hm hh i z).trans; exact le_of_eq (by unfold T; ring)
end YM.OPE.Balsam
