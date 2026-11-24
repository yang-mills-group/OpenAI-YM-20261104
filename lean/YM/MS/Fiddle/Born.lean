import YM.MS.Fiddle.Unity
/-!
# Bill smooth on log path. Budget estimates multiplying by exterior phases. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fiddle
open Function Set Filter Finset Metric Real MeasureTheory Momentum Tone Landau Osc Osc.Snap Lattice
open scoped Topology ContDiff
variable {I E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {S:Scale I}{K:Cost I E}{f:I→ E→ℂ}{a b w:I→ℝ}{V:I→QP}
def bellZ (x:ℝ): ℂ:= Complex.exp (Complex.I * x)
def Aux (p:QP): QP →L[ℝ] ℝ:= ∑ i:Axis, p i • ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Axis=>ℝ) i
lemma atAux (p q:QP): Aux p q = Momentum.pairing p q:= by rw [Aux,_root_.sum_apply]; rfl
lemma bill_at (p q:QP): Tone.bill p q=bellZ ( Aux p q ):= congr_arg bellZ (atAux p q).symm
lemma bellZ_p : ContDiff ℝ ∞ bellZ:= by exact ContDiff.cexp ( ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff )
lemma wall_x (n:ℕ)(p:ℝ) : ‖iteratedFDeriv ℝ n bellZ p‖ ≤ 1:= by
   have hp: iteratedDeriv n bellZ p=Complex.I^n*bellZ p:= by
       induction n generalizing p with
       | zero=> simp
       | succ n ih=>
                        rw [iteratedDeriv_succ,funext ih];
                        let f (x:ℝ):=Complex.I*(x:ℂ); have hs:HasDerivAt f Complex.I p:= by convert! (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (𝕜:=ℝ) p (hasDerivAt_id' p)).const_mul Complex.I using 1; simp
                        change deriv (fun x:ℝ=> Complex.I^n * Complex.exp (f x)) p=_; rw [ (hs.cexp.const_mul (Complex.I^n)).deriv ]; unfold bellZ f; rw [pow_succ]; ring
   rw [ norm_iteratedFDeriv_eq_norm_iteratedDeriv,hp,norm_mul,norm_pow ]; simp [bellZ,Complex.norm_exp]
lemma W_tip (p:QP): ‖Aux p‖ ≤ 4*‖p‖:= by
   apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro q; rw [atAux]; calc
      _ ≤ ∑ i:Axis, ‖p i*q i‖ := norm_sum_le _ _
      _ ≤ ∑ _i:Axis, ( ‖p‖*‖q‖ ) := Finset.sum_le_sum fun i _=> le_trans ( norm_mul_le .. ) (mul_le_mul ( norm_le_pi_norm p i ) ( norm_le_pi_norm q i ) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by simp [Axis]; ring
lemma bill_sm (p:QP): ContDiff ℝ ∞ (Tone.bill p):= by rw [funext (bill_at p)]; exact bellZ_p.comp (Aux p).contDiff
lemma sailor (p:QP): Peak (Tone.bill p):= ⟨ fun x=> ( Tone.bill_norm p x ).le,( bill_sm p ).continuous ⟩
lemma billQ (L:E→L[ℝ] QP)(p:QP)(i:ℕ)(x:E): ‖iteratedFDeriv ℝ i ((Tone.bill p)∘ L) x‖ ≤ ( 4*‖p‖* ‖L‖ )^i := by
   let J:= (Aux p).comp L; rw [ show Tone.bill p∘ L = bellZ ∘ J from funext fun v=>bill_at p ( L v ), J.iteratedFDeriv_comp_right bellZ_p x (by exact_mod_cast le_top) ]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)|>.trans; simp; refine ( mul_le_mul_of_nonneg_right ( wall_x .. ) (pow_nonneg ( norm_nonneg J ) _))|>.trans ?_; rw [one_mul]; gcongr; exact ( ContinuousLinearMap.opNorm_comp_le .. )|>.trans ( mul_le_mul_of_nonneg_right (W_tip p) (norm_nonneg L)) -- lint
-- multiply phases with cost or with Polyn credit for R/s. table with cheap allowance S.basic(k) denominator. 
variable (L:E→L[ℝ] QP)
lemma tariff (ht:∀ i,0< a i)(h:∀ i,a i≤1) (hc: K.Le (fun i _=>‖V i‖ ) (fun i _=>S.length i/a i)) (k n:ℕ)(hp:n≤ k): K.Part S (fun i p=> Tone.bill (V i) ( L p )) (fun i _=> (a i^k)⁻¹) n:= by
   have hV:K.Le (fun i (_:E)=> 4 * ‖V i‖ *‖L‖) (fun i _=> S.length i/a i):= by
       rw [show (fun i=>fun _:E=> 4*‖V i‖*‖L‖) = (fun i=>fun _:E=> (4*‖L‖)*‖V i‖) from funext fun i=> funext fun v=> mul_right_comm .. ]; exact hc.const_mul (4*‖L‖) (by positivity) (fun i _ _ => div_nonneg (S.pos i|>.le) (ht i|>.le))
   apply ((hV.pow (fun i _ _=> by positivity) n).left (fun i p _=>?_))|>.right; · intro i p _; rw [div_pow,← div_eq_inv_mul]; refine div_le_div_of_nonneg_left (pow_nonneg (S.pos i|>.le) _) (pow_pos (ht i) _) ?_; exact pow_le_pow_of_le_one (ht i|>.le) (h i) hp
   exact billQ L (V i) n p -- order
lemma pulseCost {g:I→ E→ℝ}(hf:∀ k:ℕ, Costs K S f (fun i p=> g i p*a i^k))(ht:∀ i,0<a i)(hx:∀ i,a i≤1) (hc: K.Le (fun i _ => ‖V i‖) (fun i _=> S.length i / a i)) (k:ℕ): Costs K S (fun i x=>Tone.bill (V i) (L x)*f i x) (fun i p=> g i p*a i^k):= by
   have he(i:I): ContDiff ℝ ∞ ((Tone.bill (V i))∘ L):= (bill_sm (V i)).comp L.contDiff; refine ⟨fun i=> (he i).mul ( (hf 0).smooth i), fun j=>?_⟩;
   let aF (i:I) := a i; obtain hJ:= Cost.Part.bilinear (ContinuousLinearMap.mul ℝ ℂ) he ( (hf 0).smooth ) (fun i hi=>tariff (K:=K) L ht hx hc j i hi) (fun i hi=> (hf (k+j)).quoted i); convert hJ using 1; -- maybe ℝ-β kernel comp
   · rfl
   ext i p; rw [pow_add]; field_simp [(ht i).ne']
lemma pulse_bill {g:I→E→ℝ}(h: Costs K S f g)(hp: K.Le (fun i _=>‖V i‖) (fun i _=>S.length i)) : Costs K S (fun i x=> Tone.bill (V i) (L x)*f i x) g:= by
   obtain ht := pulseCost (K:=K) (g:=g) (a:=1) L (fun k=>(by simpa only [ Pi.one_apply, one_pow, mul_one ] using h)) (fun i=> zero_lt_one) (fun i=>le_rfl) ( by simpa only [ Pi.one_apply, div_one ] using hp) 0; simpa using ht -- f binder unresolved
end YM.MS.Fiddle
