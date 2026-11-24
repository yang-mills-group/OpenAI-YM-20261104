import YM.FVA2.O.Ward.Table
/-!
# Radius and rest integrals are absolutely convergent
Here don't infer relative size from compact supports; use genuine Schwartz bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect
local notation "Π0"=> Job.single Unit
variable {G:Gauge} {μ:Measure QP}{s:ℝ}{U V:Edge G}{f g:Law G}
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x y:E→ℂ}
structure Envelope (x:E→ℂ) : Prop where
    smooth0 : Continuous x
    env : ∃ C:ℝ,0<C∧ ∃ k:ℕ, ∀ p, ‖x p‖ ≤ C*(1+‖p‖)^k
structure Shrink (x:E→ℂ) : Prop where
    smooth0 : Continuous x
    env (k:ℕ): ∃ C:ℝ,0<C∧∀ p, ‖x p‖ ≤ C/(1+‖p‖)^k
lemma Shrink.line (h: total Π0 (fun _=>x) 1): Shrink x:= ⟨(h 0|>.smooth ()).continuous, fun k=> by simpa only [norm_iteratedFDeriv_zero] using balance h k 0⟩
omit [NormedSpace ℝ E] in
lemma Shrink.envelope (h:Shrink x): Envelope x:= ⟨h.smooth0,by obtain ⟨C,hC,hK⟩:= h.env 0; exact ⟨C,hC,0,fun i=>(by simpa using hK i)⟩ ⟩
omit [NormedSpace ℝ E] in
lemma Shrink.mul (h:Shrink x)(he:Envelope y): Shrink (fun p=> x p*y p) := by
    refine ⟨ h.smooth0.mul he.smooth0, fun k=>?_⟩; obtain ⟨C,hC,m,hm⟩:= he.env; obtain ⟨D,hD,hk⟩:= h.env (k+m); refine ⟨D*C,by positivity,fun i=>?_⟩; rw [norm_mul]; apply (mul_le_mul (hk i) (hm i) (norm_nonneg _) (by positivity))|>.trans_eq; rw [pow_add]; field_simp
lemma Shrink.ready [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](h:Shrink x)(ν:Measure E)[Measure.IsAddHaarMeasure ν]: Integrable x ν:= by
    obtain ⟨C,hC,hM⟩:= h.env (Module.finrank ℝ E +1); exact ((Reserve.dustInteg (S:=Π0) () _ (Nat.lt_succ_self _)).const_mul C).mono' h.smooth0.aestronglyMeasurable (.of_forall fun q=> by simpa [Scale.dust,Scale.weight,Job.cw,div_eq_mul_inv] using hM q)
lemma Envelope.plan (h:Bound Π0 (fun _=>x) 1): Envelope x := by
    obtain ⟨C,hC,k,hk⟩:= h.quoted 0; exact ⟨(h.smooth ()).continuous,C,hC,k,fun p=>by simpa [Scale.full,Scale.weight,Job.single] using hk () p trivial ⟩
lemma Envelope.at_one {x:E×ℝ→ℂ}(h:Bound Π0 (fun _=>x) 1): Envelope (fun p:E=> x (p,1)) := by
    obtain ⟨ht,C,hC,k,hk⟩:= Envelope.plan h; refine ⟨ht.comp (continuous_id.prodMk continuous_const),C*2^k,by positivity,k,fun i=> ?_⟩; refine (hk (i,1)).trans ?_; rw [mul_assoc C,← mul_pow]; gcongr ?_ * ?_ ^ _; rw [Prod.norm_def,show ‖(1:ℝ)‖=(1:ℝ) by simp ]; -- simplify projections
    have hb:= norm_nonneg i
    rcases le_total ‖i‖ (1:ℝ) with hp|hp
    · rw [ max_eq_right hp ]; linarith
    rw [ max_eq_left hp ]; linarith
omit [NormedSpace ℝ E] in
lemma Envelope.mul (h:Envelope x)(hp:Envelope y): Envelope (fun p=> x p*y p):= by
    obtain ⟨hx,C,hC,k,H⟩:=h; obtain ⟨hy,D,hD,r,Hr⟩:=hp; refine ⟨hx.mul hy,C*D,mul_pos hC hD,k+r,fun p=>?_⟩; rw [norm_mul, pow_add]; refine (mul_le_mul (H p) (Hr p) (norm_nonneg _) (by positivity)).trans_eq (by ring)
lemma Envelope.scale (c:ℂ) (h:Envelope x): Envelope (fun p=> c*x p) := (Envelope.plan (blankB c)).mul h
lemma hit_p (hp:f∈Wallet G)(hh:g∈ Wallet G)(h:Rolled U)(hm:Rolled V)(l r:Legs (Mode (BH G) QP))(a e i j:BH G): Shrink (hits Landau.parity U V f g l r a e i j):= by
    let E:= QP × ℝ; let X:= ContinuousLinearMap.fst ℝ QP ℝ; let T:= ContinuousLinearMap.snd ℝ QP ℝ; let M: E→L[ℝ] QP:= -(X+T.smulRight ( Plane.net l )); let L:= Wire.lift (Wire.ray l) T; let R:= Wire.lift (Wire.ray r) T
    have hM (p:QP): M (p,1)=-(p+Plane.net l) := by change - (p+(1:ℝ) • Plane.net l)= _; rw [one_smul]
    have hf := Envelope.at_one (permits.mp hp E ((i,M)::(a,X):: L)); have hg:= Envelope.at_one (permits.mp hh E ((j,-M)::(e,-X)::R)); have hL := Envelope.at_one ( Bound.linear M (polar (lineOf h i j)))
    unfold hits radius; simp only [net_cons,degree_cons, field]; refine Shrink.mul (Shrink.line (lineOf hm a e)) (Envelope.scale _ ?_); refine Envelope.mul ( Envelope.mul (( Envelope.scale (2:ℂ) ?_)) (Envelope.scale _ ?_ ) ) ?_
    · simpa only [hM] using hL
    · simpa [ E,L,X,T, fieldVal, Wire.lift_sail,hM] using hf
    simpa [ E,R,X,T,fieldVal, Wire.lift_sail,hM] using hg
lemma colors (hp:f∈ Wallet G)(hh:g∈ Wallet G)(h:Rolled U)(hm:Rolled V)(hr:Reverse V Landau.parity): Heat.Route U V Landau.parity f g planeF where
    lf _ _ _ _ _ _ := (hit_p hp hh h hm ..).ready _
    rf l r a e i j:= by
         let R :=restL Landau.parity U V f g l r a e i j; let L:=hits Landau.parity U V f g l r e a i j; have ht : Integrable L planeF:=(hit_p hp hh h hm ..).ready _
         change Integrable R planeF; rw [show R=L ∘ Neg.neg from funext (fun i=>by nth_rw 1 [← neg_neg i]; exact RL hr ..)]; exact (Measure.measurePreserving_neg _).integrable_comp_of_integrable ht
    shift:= by intro i j a b c d; exact integral_sub_left_eq_self ..
    flip:= by intro i j a b c d; exact integral_neg_eq_self ..
end YM.FVA2.O.Ward
