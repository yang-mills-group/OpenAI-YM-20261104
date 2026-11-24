import YM.RG11Proof.Scale.Beam

/-!
# Separated power-log margin and geometry costs

Complex polynomial in REAL log(s) = u, scale=exp(-u), engineering
weight exponent in ℝ (summing input incl derivatives; may be negative)
so growing like exp(w*u). `price Ω L w`: on domains Ω(u) with u sufficiently
large uniform constant on remaining geometry (geometry seminorm, gaps and
contact windows must be paid in L(u,η)). Constants not uniform over labels,
number of points, coefficient/truncation orders, field/derivative demand
unless separately packed into that API. Pure scalar estimate. Later residual
transport on those bounds exact finite coefficient costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Grove
open scoped Classical BigOperators Topology
open Set Filter

/-- Exact power log dependence (mass-independent at unit subtraction length,
all λ=exp(-u)>0, fixed order). Series indexed by geometry may each have own
polynomial. Reality NOT assumed.
-/
def season (w:ℝ):Submodule ℂ (ℝ→ℂ) where
  carrier:={v|∃ p:Polynomial ℂ,∀ u:ℝ,v u=(Real.exp (w*u):ℂ)*p.eval (u:ℂ)}
  zero_mem':=⟨0,fun _=>by simp⟩
  add_mem':=by rintro x y ⟨p,h⟩ ⟨q,he⟩; exact ⟨p+q,fun u=>by simp [h,he,mul_add]⟩
  smul_mem':=by rintro z x ⟨p,h⟩; exact ⟨Polynomial.C z*p,fun u=>by simp only [Pi.smul_apply,smul_eq_mul,h, Polynomial.eval_C_mul]; ring⟩

 theorem season_of {f:ℝ→ℂ}{w:ℝ}: f∈season w ↔ ∃ p:Polynomial ℂ,∀ u:ℝ,f u=(Real.exp (w*u):ℂ)*p.eval (u:ℂ):=Iff.rfl

 theorem product {v w:ℝ}{f g:ℝ→ℂ}(h:f∈ season v)(hp:g∈season w): f*g∈season (v+w):=by
    obtain ⟨p,H⟩:=h; obtain ⟨q,G⟩:=hp; use p*q; intro u; simp only [Pi.mul_apply,H,G,Polynomial.eval_mul,add_mul,Real.exp_add, Complex.ofReal_mul]; ring

def sleeve (w:ℝ)(n:ℕ)(u:ℝ):=Real.exp (w*u)*(1+|u|)^n
 theorem sleeve_nonneg (w:ℝ)(n:ℕ)(u:ℝ):0 ≤ sleeve w n u:=by unfold sleeve; positivity
 theorem sleeve_degree (w:ℝ){n k:ℕ}(h:n ≤ k)(u:ℝ):sleeve w n u ≤ sleeve w k u:=by unfold sleeve; gcongr; simp
 theorem sleeve_power (v w:ℝ)(n:ℕ)(u:ℝ)(h:v*u ≤ w*u): sleeve v n u ≤  sleeve w n u:=by unfold sleeve; gcongr

/-- θ_est >= 0 on Ω(u) sufficient. u threshold universal on this type;
encodes fixed geometry too (`EventRate`) and sup-type estimates with seminorms
ν_{k,R,δ} in L. Require bounds also on all input powers up to requested if
transforming; do not truncate frame products before insert. -/
def price {Γ:Type*}(Ω:ℝ→Set Γ)(L:ℝ→Γ→ℝ)(w:ℝ)(f:ℝ→Γ→ℂ):Prop:=
  ∃ (C:ℝ)(d:ℕ),0 ≤ C ∧ ∀ᶠ u:ℝ in atTop,∀ x∈Ω u,‖f u x‖  ≤  C*sleeve w d u * L u x

variable {Γ : Type*}{Ω:ℝ→Set Γ}{L:ℝ→Γ→ℝ}

def Actual (Ω:ℝ→Set Γ)(L:ℝ→Γ→ℝ):Prop:=∀ᶠ u in atTop,∀ x∈Ω u,0 ≤ L u x

theorem actual_const : Actual Ω (fun _ _=>1):=Eventually.of_forall fun _ _ _=>zero_le_one

def credit (Ω:ℝ→ Set Γ)(L:ℝ→Γ→ℝ)(h:Actual Ω L)(w:ℝ):Submodule ℂ (ℝ→Γ→ℂ) where
   carrier:={a|price Ω L w a}
   zero_mem':=by refine ⟨0,0,le_rfl,Eventually.of_forall fun _ _ _=>by simp⟩
   add_mem':=by
      rintro x y ⟨C,n,hp,he⟩ ⟨D,m,hD,hH⟩
      refine ⟨C+D,n+m,add_nonneg hp hD,?_⟩
      filter_upwards [he,hH,h] with u hu hv hk
      intro i hh
      rw [Pi.add_apply,Pi.add_apply,add_mul,add_mul]
      apply (norm_add_le ..).trans
      apply add_le_add ((hu _ hh).trans ?_) ((hv _ hh).trans ?_)
      all_goals exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sleeve_degree w (by omega) u) (by assumption)) (hk i hh)
   smul_mem':=by
      rintro z x ⟨C,n,hC,hp⟩
      refine ⟨‖z‖ * C,n,mul_nonneg (norm_nonneg _) hC,hp.mono fun u hu i hh=>?_⟩
      simp only [Pi.smul_apply,norm_smul,mul_assoc]
      exact mul_le_mul_of_nonneg_left (by simpa only [←mul_assoc] using hu _ hh) (norm_nonneg _)

 theorem incurs (h:Actual Ω L){w:ℝ}{f:ℝ→ Γ→ℂ}:price Ω L w f ↔ f∈credit Ω L h w:=Iff.rfl

def individual (w:ℝ) : Submodule ℂ (ℝ→ℂ) where
   carrier:={f|price (fun _=> (Set.univ:Set Unit)) (fun _ _=>1) w (fun u _=>f u)}
   zero_mem':= (credit (fun _=>(Set.univ:Set Unit)) _ actual_const w).zero_mem
   add_mem':= by intro x y hx hy; apply (credit (fun _=> (Set.univ:Set Unit)) _ actual_const w).add_mem (x:=fun u _=>x u) (y:=fun u _=>y u) hx hy
   smul_mem':=by intro c x hx; apply (credit (fun _=>(Set.univ:Set Unit)) _ actual_const w).smul_mem c (x:=fun u _=>x u) hx

 theorem personally {w:ℝ}{f:ℝ→ℂ}: f∈individual w ↔ ∃ (C:ℝ)(d:ℕ),0 ≤ C ∧ ∀ᶠ u:ℝ in atTop,‖f u‖  ≤  C*sleeve w d u:=by
  change price (fun _=>(Set.univ:Set Unit)) (fun _ _=>1) w (fun u _=>f u) ↔ _; simp only [price,mul_one,Set.mem_univ, true_imp_iff]
  simp

private theorem poly_price (p:Polynomial ℂ): (fun u:ℝ=>p.eval (u:ℂ))∈individual 0:=by
   induction p using Polynomial.induction_on' with
   |add p q hp hq=> convert! (individual 0).add_mem hp hq using 1; ext u; simp
   |monomial i z=>
      refine personally.mpr ⟨‖z‖,i,norm_nonneg _,Eventually.of_forall fun u=>?_⟩
      simp only [Polynomial.eval_monomial,norm_mul,norm_pow,Complex.norm_real,sleeve,zero_mul,Real.exp_zero,one_mul]
      gcongr
      exact le_add_of_nonneg_left zero_le_one

 theorem sleeps (w:ℝ): season w  ≤ individual w:=by
   rintro f ⟨p,hp⟩
   obtain ⟨C,n,h,hC⟩:=personally.mp (poly_price p)
   refine personally.mpr ⟨C,n,h,hC.mono (fun u hu=> ?_)⟩
   simp only [sleeve,zero_mul,Real.exp_zero,one_mul] at hu ⊢
   rw [hp,norm_mul,Complex.norm_real,Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),mul_left_comm]
   exact mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le

-- threshold order shrinkage vs cost on all demands in the list
 theorem lets (h:Actual Ω L) {v w:ℝ}(he:v ≤ w):credit Ω L h v  ≤  credit Ω L h w:=by
   rintro f ⟨C,n,hC,hf⟩
   refine ⟨C,n,hC,?_⟩
   filter_upwards [hf,h,eventually_ge_atTop (0:ℝ)] with u hu hh hk i hi
   exact (hu i hi).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sleeve_power _ _ _ _ (by gcongr)) hC) (hh i hi))
 theorem individually {v w:ℝ}(h:v ≤ w):individual v ≤ individual w:=by
    intro f he; exact lets (Ω:=fun _=>Set.univ) actual_const h he

/-- Decay after undoing a strictly higher engineering power. -/
 theorem lower_undo {w v:ℝ}{f:ℝ→ℂ}(h:f∈individual w)(h₀:w<v):
    Filter.Tendsto (fun u:ℝ=>Real.exp (-(v*u))*‖f u‖) Filter.atTop (𝓝 0):=by
     obtain ⟨C,n,hC,he⟩:=personally.mp h
     have hu : Filter.Tendsto (fun u:ℝ=> (C*2^n)*(u^n * Real.exp (- (v-w)*u))) atTop (𝓝 0):=by
        simpa only [Real.rpow_natCast, mul_zero] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n (v-w) (by linarith)).const_mul (C*2^n)
     apply squeeze_zero' (Eventually.of_forall (fun _=>by positivity)) _ hu
     filter_upwards [he,eventually_ge_atTop (1:ℝ)] with u hi hk
     rw [sleeve,abs_of_pos (by linarith)] at hi
     have hq : Real.exp (-(v*u))*‖f u‖ ≤ Real.exp (-(v*u))*(C*(Real.exp (w*u)*(1+u)^n)):=by gcongr
     apply hq.trans
     have hh: Real.exp (-(v*u))*(C*(Real.exp (w*u)*(1+u)^n)) = C * (1+u)^n * Real.exp (-(v-w)*u) := by rw [show -(v-w)*u= -(v*u)+w*u by ring,Real.exp_add]; ring
     rw [hh,←mul_assoc _ (u^n),mul_assoc C (2^n) (u^n),←mul_pow]
     gcongr; linarith

 theorem wipe {w v:ℝ}{f:ℝ→ℂ}(h:f∈season v)(he:f∈individual w)(hk:w < v): f=0:=by
    obtain ⟨p,hp⟩:=season_of.mp h
    have hh:=lower_undo he hk
    have hg: Filter.Tendsto (fun u:ℝ=>‖p.eval (u:ℂ)‖) Filter.atTop (𝓝 0):=by
       convert! hh using 1
       ext u; rw [hp,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_neg,←mul_assoc,inv_mul_cancel₀ (Real.exp_ne_zero _),one_mul]
    have heq : p=0:=by
       by_cases hx:0<p.degree
       · have ht:=p.tendsto_norm_atTop hx (z:=fun u:ℝ=>(u:ℂ)) (by simpa [Real.norm_eq_abs] using (tendsto_abs_atTop_atTop:Filter.Tendsto (fun u:ℝ=>|u|) atTop atTop))
         exact False.elim ((not_tendsto_nhds_of_tendsto_atTop ht) _ hg)
       rw [Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hx)] at hg ⊢
       simp only [Polynomial.eval_C,tendsto_const_nhds_iff,norm_eq_zero] at hg
       simp [hg]
    ext u; rw [hp,heq,Polynomial.eval_zero,mul_zero]; rfl
end YM.RG11.Grove
