import YM.RegulatorIR.Pupil.Matte

/-!
# Probability norm of rank-two projection without volume credit
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil.Rules
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum Oracle Quarry Precision Work.F08 Tree Exterior
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G : Gauge}{T V:Packet (Foot G) 2}{A B:ℝ≥0∞}
-- linearity rights
lemma sum_R (H:Rules T)(P:Rules V): Rules (T+V):=by
 let f (x y:Foot G): twin (T+V) x y=twin T x y+twin V x y:= rfl
 have h(x y a b): sparkle (T+V) x y a b=sparkle T x y a b+sparkle V x y a b:=by unfold sparkle; simp_rw [f,mul_add,sum_add_distrib]
 refine ⟨fun x y=>congr_arg₂ (·+·) (H.twinSym x y) (P.twinSym x y),fun x y=> congr_arg₂ (·+·) (H.throughout x y) (P.throughout x y), fun k x y a b=> ?_,fun k x y=>by rw [f,H.glow,P.glow,f,mul_add], fun x y a=>?_⟩
 · rw [h,h (a:=G.adjoint k a), H.pearl k,P.pearl k]
 simp_rw [f,add_sub_add_comm, sum_add_distrib,H.diverge,P.diverge,add_zero]
lemma smul_R (H:Rules T)(k:ℝ): Rules (k • T):=by
 let f(x y:Foot G): twin (k • T) x y=k*twin T x y:=rfl
 have h(x y a b): sparkle (k • T) x y a b=k*sparkle T x y a b:=by unfold sparkle; simp_rw [f,mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _;ring
 refine ⟨fun x y=>congr_arg (k*·) (H.twinSym ..),fun x y=>congr_arg (k*·) (H.throughout ..),fun k x y a b=>?_,fun l x y=>by rw [f,H.glow,f]; ring, fun x y a=>?_⟩
 · rw [h,h (a:=G.adjoint k a),H.pearl k]
 simp_rw [f,← mul_sub,← mul_sum,H.diverge, mul_zero]
lemma minus_R (h:Rules T)(hv:Rules V):Rules (T-V):=by rw [sub_eq_add_neg,← neg_one_smul ℝ V]; exact sum_R h (smul_R hv _)
lemma minus_shine (H:costM T)(V':costM V)(n:ℕ)(hn:n≤3)(w a b): shine (T-V) n w a b=shine T n w a b-shine V n w a b:=by
 unfold shine recital; simp_rw [show ∀ x y p,starE (T-V) x y p=starE T x y p-starE V x y p from fun _ _ _=>rfl,sub_mul]; exact (H _ _ _ _ hn).tsum_sub (V' _ _ _ _ hn)
lemma smul_shine (k:ℝ)(n:ℕ)(w a b): shine (k • T) n w a b=k * shine T n w a b:=by unfold shine recital; simp_rw [show ∀ x y p,starE (k • T) x y p=k*starE T x y p from fun _ _ _=>rfl,mul_assoc]; exact tsum_mul_left

-- quantitative utilities over Held. Need only output for log increments preview.
lemma star_abs (T:Packet (Foot G) 2) (x y:CapG G)(a:Room)(n:ℕ)(p:Cover): ‖starE T x y p * dial a p ^n‖ₑ≤ ‖starE T x y p‖ₑ* (extent p)^n * (‖a‖ₑ)^n:=by
 have h: ‖dial a p‖ₑ≤ extent p * ‖a‖ₑ:=by rw [← ofReal_norm,← ofReal_norm,mul_comm]; unfold Momentum.extent; rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (norm_nonneg _)]; exact ENNReal.ofReal_le_ofReal (dial_norm ..)
 rw [enorm_mul]; conv_rhs => rw [mul_assoc, ← mul_pow ]
 apply mul_le_mul_right
 rw [← ofReal_norm,norm_pow,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]; exact pow_le_pow_left' h _
lemma star_fee (T:Packet (Foot G) 2) {a:Room}{n u:ℕ}{A:ℝ≥0∞}(h:Held T u A) (x y : CapG G)(hp:n ≤ u): quota (fun p=>starE T x y p*dial a p^n) 1 ≤ A*‖a‖ₑ^n:=by
 let r:= ask 0 x; let f(t:Cover):Tuple (Foot G) 1:= fun _=> ask t y
 have hf : Injective f:=fun i j hh=>congr_arg (fun x:Tuple (Foot G) 1=> area (x 0)) hh
 let U:=wall 0 1 u (X:=G.ColorIndex) (r:=1);let Q:= Momentum.anchored r T
 have hh : quota (Q ∘ f) (U ∘ f)≤A:= (quota_restrict f hf Q U).trans (h r)
 apply le_trans _ (mul_le_mul_left hh _); rw [quota_base,quota,← ENNReal.tsum_mul_right]; refine ENNReal.tsum_le_tsum ?_;intro p
 have hx: U (f p)=(1+extent p)^u:=by simp only [U,f,Momentum.wall, awayZ,award, Nat.cast_one,inv_one,one_mul,one_smul,zero_sub,Fin.sum_univ_one]; rw [Momentum.extent_neg];rfl -- ambiguous wall
 apply le_trans (star_abs T x y a n p); apply mul_le_mul_left; have hp : extent p^n≤ (U ∘ f) p:=by rw [comp_apply,hx]; apply le_trans (pow_le_pow_left' (show extent p≤1+extent p from le_add_self) _);exact pow_le_pow_right₀ (show 1≤1+extent p from le_self_add) hp
 rw [show starE T x y p=(Q ∘ f) p from congr_arg T (funext (fun i=>by fin_cases i <;> rfl))];exact mul_le_mul_right hp _
lemma star_paid (hA:A≠⊤) {u:ℕ}(hp:3≤u)(h:Held T u A) : costM T:=fun x y a n hv=> quota_summable (w:=1) (fun p=>le_rfl) (ne_top_of_le_ne_top (ENNReal.mul_ne_top hA (by exact ENNReal.pow_ne_top (show ‖a‖ₑ≠⊤ by finiteness))) (star_fee T h x y (le_trans hv hp)))
lemma token_price {u:ℕ}(hp:2≤u)(h:Held T u A)(c): ‖token T c‖ₑ ≤ A:=by
 unfold token shine recital;apply enorm_tsum_le_tsum_enorm.trans; rw [← quota_base];apply le_trans (star_fee T h _ _ hp)
 have ht: ‖(step 0:Room)‖≤1:=by apply (pi_norm_le_iff_of_nonempty ..).mpr; intro i; rw [step_apply]; split <;> norm_num
 apply (mul_le_mul_right (pow_le_pow_left' (show ‖(step 0:Room)‖ₑ≤1 from by rw [← ofReal_norm]; exact (ENNReal.ofReal_le_ofReal ht).trans_eq (ENNReal.ofReal_one)) 2) A).trans_eq; simp

-- WilsonX reads $lambda_K=1$ in this normalization. No side dependence.
variable {D: Bed}{δ σ C :ℝ}{p:RG.Clip}
lemma kinetic (h:Hall D σ C δ p)(x:G.ColorIndex) : token (coil (Oracle.crust G D)) x=1:=by
 let K:=Oracle.crust G D
 have ht(u:Cover): starE (coil K) (1,x) (1,x) u=(-1/2:ℝ)* colorK G (FreeResolvent.hBlock D.metric) (coord 1,x) (coord 1,x) u:=by
    change (-1/2:ℝ)*colorK G _ (coord 1,x) (coord 1,x) (u-0) = _; rw [sub_zero]
 unfold token shine recital;change ∑' u,starE (coil K) _ _ u*_= _; simp_rw [ht]; change (∑' u:Cover,(-1/2:ℝ)*colorK G _ (coord 1,x) (coord 1,x) u*dial (step 0) u ^2)=1; simp only [colorK, ↓reduceIte,mul_assoc (-1/2:ℝ),tsum_mul_left]; rw [show (∑' u,_) = _ from Momentum.trans_pair h];norm_num

end YM.RegulatorIR.Pupil.Rules
