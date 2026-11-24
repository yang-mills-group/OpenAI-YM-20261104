import YM.XSpace.Maize
/-!
# Statement of three-leg position costs, finite and conjugate
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Lattice Trace Relief Gland Season Chart2 Chiral Mu Octave Tide Graph3 MvPolynomial Asymptotics
open scoped Topology ContDiff BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{u v b:E4} {x y z:ι→Cover} {G:Gauge}{n i j:ℕ} {c:Shade.Cut}
structure Captain (c:Shade.Cut)(L:Filter ι)(a:ι→ℝ)(x y z:ι→Cover)(u v b:E4):Prop where
  led : Stage L a
  x₁ : distance L a x u
  x₂ : distance L a y v
  x₃ : distance L a z b
  gleam: Gleam c u v b
namespace Captain
variable (Q:Captain c L a x y z u v b)
include Q
lemma turn : Captain c L a y z x v b u:=⟨Q.led,Q.x₂,Q.x₃,Q.x₁,⟨Q.gleam.vb,range_sym _ Q.gleam.uv,range_sym _ Q.gleam.ub⟩⟩
lemma hop :Captain c L a y x z v u b:= ⟨Q.led,Q.x₂,Q.x₁,Q.x₃,⟨range_sym _ Q.gleam.uv,Q.gleam.vb,Q.gleam.ub⟩⟩
lemma both : distance L a (fun i=>x i-y i) (u-v):= Season.value Q.x₁ Q.x₂
lemma diff : u-v≠ 0:= sub_ne_zero.mpr (gap c Q.gleam.uv)
lemma sec : distFee L a (fun i=> x i-y i):= finite_pay Q.led Q.both Q.diff
lemma grant : Ensemble L a x y z:= ⟨Q.sec,Q.hop.turn.sec,Q.turn.sec⟩
end Captain
lemma minute {V:Type}[NormedAddCommGroup V]{f:ι→V}(s:Stage L a) (p:funds L a n f)(h:i<n): Little L a i f:= IsBigO.trans_isLittleO p ((isLittleO_pow_pow h).comp_tendsto s.zero)
lemma gowns {f g:ι→ℂ}(p:funds L a i f)(h:funds L a j g): funds L a (i+j) (fun t=> f t*g t):= (IsBigO.mul p h).congr (fun _=>rfl) (fun i=>(pow_add ..).symm)
lemma painted {f:ι→ℝ}(h:funds L a i f): funds L a i (fun j=> (f j:ℂ)):= by obtain ⟨C,h⟩:= IsBigO.bound h; exact IsBigO.of_bound C (h.mono fun i hi=>by rw [Complex.norm_real]; exact hi)
abbrev Payout (L:Filter ι)(a:ι→ℝ)(n:ℕ)(f:ι→ℝ)(v:ℝ):= Tendsto (fun i=> (a i)⁻¹^n*f i) L (𝓝 v)
abbrev Named (L:Filter ι)(a:ι→ℝ)(n:ℕ)(f:ι→ℂ)(v:ℂ):= Tendsto (fun i=> (Foundation.base (a i))^n*f i) L (𝓝 v)
lemma Payout.big {F:ι→ℝ}(p:Little L a i F) (s:Stage L a): Payout L a i F 0:= tau s p
lemma Payout.of_shift {x:ι→Cover}{F H:Toe} {f:Breeze}(p:Beam n F f)(h:H-F∈Terrain (n+1))(s:Stage L a)(P:distance L a x u)(H':u≠0): Payout L a n (fun i=> H (x i)) (f u):=by
  have hx := (shines s P H' p).add (pays0 s n (funder s (finite_pay s P H') h)); rw [add_zero (f u)] at hx; exact hx.congr fun j=>by rw [Pi.sub_apply,mul_sub]; ring
namespace Named
variable {f g:ι→ℂ}{u v:ℂ}
lemma add (h:Named L a n f u)(p:Named L a n g v): Named L a n (fun i=>f i+g i) (u+v):= (Tendsto.add h p).congr fun _=>(mul_add ..).symm
lemma neg (h:Named L a n f u): Named L a n (fun i=>-f i) (-u):= (Tendsto.neg h).congr fun _=>(mul_neg ..).symm
lemma sub (h:Named L a n f u)(p:Named L a n g v): Named L a n (fun i=> f i-g i) (u-v):= (Tendsto.sub h p).congr fun _=> (mul_sub ..).symm
lemma mul (h:Named L a i f u)(p: Named L a j g v): Named L a (i+j) (fun i=>f i*g i) (u*v):=by
  have he : Tendsto (fun t=> (Foundation.base (a t))^i*f t*((Foundation.base (a t))^j*g t)) L (𝓝 (u*v)):= Tendsto.mul h p; exact he.congr fun i=>by rw [pow_add]; ring
lemma const_mul (h:Named L a n f u)(c:ℂ): Named L a n (fun i=> c*f i) (c*u):= (Tendsto.const_mul c h).congr fun _=> mul_left_comm ..
lemma sum {I:Type*}(F:I→ι→ℂ)(f:I→ℂ)(p:Finset I)(H:∀ i∈p,Named L a n (F i) (f i)): Named L a n (fun i=>∑ j∈p,F j i) (∑ i∈p,f i):= (tendsto_finsetSum _ H).congr fun i=>(Finset.mul_sum ..).symm
lemma congr (h:Named L a n f u)(p:∀ i,f i=g i): Named L a n g u:= (funext p) ▸ h
lemma acc (p:Named L a n g u)(H:Named L a n (fun i=> f i-g i) v): Named L a n f (v+u):= congr (Named.add H p) (fun _=> sub_add_cancel ..) -- test direction
lemma wallet (p:Named L a n g u)(H:Named L a n (fun i=> f i-g i) 0): Named L a n f u:= (zero_add u) ▸ acc p H
lemma coe {u:ℝ}{F:ι→ℝ}(p:Payout L a i F u): Named L a i (fun i=> (F i:ℂ)) ↑u:= (Complex.continuous_ofReal.continuousAt.tendsto.comp p).congr fun k=> by unfold Function.comp Foundation.base; push_cast; rfl
lemma low (p:Little L a n f)(s:Stage L a): Named L a n f 0:= by
  refine (tau s p).congr fun i => ?_; unfold Foundation.base; rw [Complex.real_smul, Complex.ofReal_pow,Complex.ofReal_inv]
end Named
end YM.XSpace.Finale
