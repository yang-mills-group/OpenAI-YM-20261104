import YM.RegulatorIR.Epoch.Affine

/-!
# Repeated charge at variable Ly
Real constant or varying skip. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.RegulatorIR.Epoch
open Function Finset Set Filter YM.RegulatorIR.Ledger Uniform
open ENNReal
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X:Type}{M:X→ℕ}{k p:ℕ}{γ θ A v:ℝ}
lemma critical_av (p:ℕ)(v:ℝ) (hv:0<v): ∃ c,0 ≤ c ∧ ∀ y z:ℝ,1 ≤ y → 0 ≤ z → (c+y+z)^p ≤ Real.exp (z*v)*(c+y)^p:=by
 cases p with
 | zero=>exact ⟨0,le_rfl,fun y z _ h=>by simpa using Real.add_one_le_exp (z*v)|>.trans' (show 1 ≤ z*v+1 from le_add_of_nonneg_left (by positivity)) ⟩
 | succ p=>
    let w:ℝ:=v/(p+1:ℕ); have hw:0<w:=div_pos hv (by positivity);let c:=w⁻¹;have hc:0<c:=inv_pos.mpr hw; refine ⟨c,hc.le,fun y z hy hz=>?_⟩
    have hp: c+y+z ≤ Real.exp (z*w)*(c+y):=by
       have hh:= Real.add_one_le_exp (z*w)
       refine le_trans ?_ (mul_le_mul_of_nonneg_right hh (by linarith:0 ≤ c+y))
       have H:w*(c+y) ≥1:=by rw [mul_add,show w*c=1 from mul_inv_cancel₀ hw.ne']; linarith only [mul_nonneg hw.le (zero_le_one.trans hy)]
       have hs : z ≤ z * (w*(c+y)):=le_mul_of_one_le_right hz H; linarith
    apply (pow_le_pow_left₀ (by linarith) hp (p+1)).trans_eq; rw [mul_pow,← Real.exp_nat_mul]
    congr 2; unfold w;field_simp
namespace Marked
variable (S:Marked M)
def coin (θ:ℝ)(w:Flap M):ℝ≥0∞:= ENNReal.ofReal (Real.exp (S.slope w*θ))
-- ↑rate, negative θ shrink
lemma coin_memo (c) i:S.coin c i=S.day i^c:= S.exp_day ..
lemma coin_v (c i): S.coin c i≠⊤:=ofReal_ne_top
lemma coin_l (c i): S.coin c i≠0:= ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
lemma mplus (c d:ℝ)(i): S.coin (c+d) i=S.coin c i*S.coin d i:=by unfold coin; rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
lemma mone (θ)(i): S.coin θ i*S.coin (-θ) i=1:=by rw [← S.mplus,add_neg_cancel,coin,mul_zero,Real.exp_zero, ENNReal.ofReal_one]
lemma mrate (i)(c:ℝ)(hc:c < 0):S.coin c i≤ ENNReal.ofReal (Real.exp (Real.log 2*c)):=by apply ENNReal.ofReal_le_ofReal; exact Real.exp_monotone (mul_le_mul_of_nonpos_right (S.incline i) hc.le)

lemma measure_buy (p:ℕ)(v:ℝ) (hv:0<v):∃ c:ℝ≥0∞,c≠⊤∧∀ w: Flap M,(c+ S.age_t.val w.prev)^p≤ S.coin v w*(c+S.age_t.val w.next)^p:=by
 obtain ⟨c,hc,h⟩:=critical_av p v hv; refine ⟨ENNReal.ofReal c,ENNReal.ofReal_ne_top,fun w=>?_⟩; let y:=S.credit w.prev;let z:=S.credit w.next; let t:=S.slope w
 have hy:0 ≤ y:=zero_le_one.trans (S.ahead _);have hz:0≤z:=zero_le_one.trans (S.ahead _)
 have hp:(c+y)^p ≤ Real.exp (t*v)*(c+z)^p:=(pow_le_pow_left₀ (by positivity) (le_trans (add_le_add_right (S.goes_f w) c) (le_of_eq (add_assoc ..).symm)) _).trans (h z t (S.ahead _) (S.rise _).le)
 change (_+ ENNReal.ofReal y)^p ≤ S.coin v w*(_+ENNReal.ofReal z)^p
 rw [← ENNReal.ofReal_add hc hy,← ENNReal.ofReal_add hc hz,← ENNReal.ofReal_pow (add_nonneg hc hy),← ENNReal.ofReal_pow (add_nonneg hc hz),coin,← ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.ofReal_le_ofReal hp

variable {f : Page M →ℝ≥0∞}
def More (F:Page M→ℝ≥0∞)(z:ℝ)(S:Marked M):Prop:=∀ i:Flap M, F i.prev≤ S.coin z i*F i.next
-- real coefficient.Lambda scaling kernels
lemma damper (F : Page M→ℝ≥0∞)(H: Flap M→ℝ≥0∞)(v γ:ℝ)(h:S.Structural)(g:v<γ)(hz:0≤v)(hq: S.More F v) (hp: Carry S.age_f (F ∘ Flap.prev) H)
 (ht: Carry (S.age_t.us (Page.opening M)) (F ∘ Page.opening M) (f ∘ Page.opening M))
 (hv: ∀ i:Flap M,f i.next ≤ S.coin (-γ) i * f i.prev + H i): Carry S.age_t F f:=by
 -- pay skip & larger p via complement
 have k:(Carry S.age_c (F ∘ Flap.next) H):=by
    have he:= refreshed hp (S.advertises h); obtain ⟨d,h',hp⟩:= he
    have hx:Poly S.age_c (S.coin v):= by rw [show S.coin v=fun i=>_ from funext fun i=> S.coin_memo v i]; exact scalar_buy hz h.fromC
    exact ⟨_,h'.mul hx,fun i=> (hp i).trans ((mul_le_mul_right (hq i) (d i)).trans_eq (mul_assoc ..).symm)⟩
 obtain ⟨a,⟨C,p,hC,P⟩,G⟩:=ht; obtain ⟨b,⟨D,q,hD,H'⟩,Hc⟩:= k
 let m:=p+q; let u:=(γ-v)/2; have he:0<u:=half_pos (sub_pos.mpr g)
 obtain ⟨c,h',hw⟩:= S.measure_buy m u he
 let Q(i:Page M):=(c+ S.age_t.val i)^m; have hf (i:Flap M):H i≤ (D*Q i.next)*F i.next:=by
    apply le_trans (Hc i);change _≤ D*Q _*_; apply mul_le_mul_left
    apply le_trans (H' i); apply mul_le_mul_right; exact (pow_le_pow_right₀ (S.age_c.above i) (show q≤m from by omega)).trans (pow_le_pow_left' (b:=c+ S.age_c.val i) le_add_self _) 
 let j:= -γ+(u+v); have hj:j<0:=by unfold j u; linarith
 let l:= Real.exp (Real.log 2*j); have hl:l<1:=by unfold l; exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (Real.log_pos (by norm_num)) hj)
 have hl':0<l:=Real.exp_pos _
 let d:= (C.toReal+D.toReal+1)/(1-l); have hc :0<d:=by unfold d; positivity
 have hL: d*(1-l)=C.toReal+D.toReal+1:=div_mul_cancel₀ _ (sub_pos.mpr hl).ne'
 have hS: ENNReal.ofReal l*ENNReal.ofReal d + D ≤ ENNReal.ofReal d:=by nth_rw 1 [← ENNReal.ofReal_toReal hD]; rw [← ENNReal.ofReal_mul hl'.le,← ENNReal.ofReal_add (mul_nonneg hl'.le hc.le) ENNReal.toReal_nonneg]; apply ENNReal.ofReal_le_ofReal; linarith [ENNReal.toReal_nonneg (a:=C)]
 have hK: C ≤ ENNReal.ofReal d:=by rw [← ENNReal.ofReal_toReal hC]; apply ENNReal.ofReal_le_ofReal; linarith [ENNReal.toReal_nonneg (a:=D),mul_nonneg hc.le hl'.le]
 let t:= ENNReal.ofReal d
 refine ⟨fun i=> t*Q i,(Poly.standard _ (show t≠⊤ from ENNReal.ofReal_ne_top)).mul (((Poly.standard _ h').add (Poly.roof _)).powQ _), Page.proves ?_ ?_⟩
 · intro w; let i:=Page.opening M w; apply le_trans (G w); apply mul_le_mul_left; apply le_trans (P w); change C * S.age_t.val i ^p ≤ t*Q i; apply mul_le_mul' hK; exact (pow_le_pow_right₀ (S.age_t.above i) (show p≤m from by omega)).trans (pow_le_pow_left' (b:=c+S.age_t.val i) le_add_self _)
 intro i hi
 apply (hv i).trans ((add_le_add (mul_le_mul_right hi _) (hf i)).trans ?_)
 change S.coin (-γ) i*(t*Q _*F _)+ _ ≤ t*Q _*_
 have hx:S.coin (-γ) i * (t*Q i.prev*F i.prev) ≤ ENNReal.ofReal l * t*Q i.next * F i.next:=by
    apply le_trans (mul_le_mul_right (mul_le_mul' (mul_le_mul_right (hw i) t) (hq i)) _)
    apply le_trans (b:= S.coin j i*t*Q i.next*F i.next)
    · apply le_of_eq; rw [S.mplus _ _ _, S.mplus _ _ _]; ring
    exact mul_le_mul_left (mul_le_mul_left (mul_le_mul_left (S.mrate i j hj) _) _) _
 apply le_trans (add_le_add_left hx _); simp only [← add_mul]; exact mul_le_mul_left (mul_le_mul_left hS _) _
end Marked
end YM.RegulatorIR.Epoch
