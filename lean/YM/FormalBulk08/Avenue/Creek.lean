import YM.FormalBulk08.Avenue.Cent
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free Reef Orb Wick Series Jets Lava Gauge
open Stationary hiding Rays
open MvPolynomial
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {V U W:Type} [Fintype V] [Fintype U] [Fintype W]


omit [Fintype V] in
lemma mix_eats (x:Glyphs ℝ V)(u:U→ℝ)(P:Matrix V U ℝ): traceP u (mixRows P x)=traceP (P*ᵥ u) x:= by
   induction x using MvPolynomial.induction_on with
   | C c => simp [mixRows,traceP]
   | add p q hQ hT=> unfold traceP at *; rw [_root_.map_add,_root_.map_add,_root_.map_add,hQ,hT]
   | mul_X p i hp=> unfold traceP at *; rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,hp]; simp [mixRows,Matrix.mulVec,dotProduct]
omit [Fintype V] in
lemma mix_budget (p:Glyphs ℝ V)(P:Matrix V U ℝ)(Q:Matrix U W ℝ): mixRows Q (mixRows P p)=mixRows (P*Q) p:= by
    apply orbit_ext; intro x; rw [mix_eats,mix_eats,mix_eats,Matrix.mulVec_mulVec]
section
variable [DecidableEq V]
lemma flag_zero (H:Hull V U)(p z:Pap (V⊕U))(hp:Solved H p): PowerSeries.coeff 0 (flag H p z)=aftEval V U (hearth (aqua H.saddle) (PowerSeries.coeff 0 (lever H z))):= by
    rw [tag_sky _ p z hp,PowerSeries.coeff_map]; refine DFunLike.congr_arg _ (?_)
    let G:=cobalt H p; let e:= aqua (I:=U) H.saddle
    let S:= lever H z
    have he:= flare_denominator e G S (cobalt_base H p)
    simp only [rack_finish] at he; have hh:= congr_arg (PowerSeries.coeff 0) he
    have hx {α: Type}[CommSemiring α](p q:PowerSeries α): PowerSeries.coeff 0 (p*q)= PowerSeries.coeff 0 p * PowerSeries.coeff 0 q:= by simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [hx, coeff_beam,coeff_beam,hx,expan_zero (show PowerSeries.coeff 0 G=0 from cobalt_base ..), one_mul, hearth_one,one_mul] at hh; exact hh
omit [DecidableEq V]
variable [DecidableEq U]
omit [Fintype V] in
lemma aft_cores (f:Pce (V⊕U)): aftEval V U f=mixRows (fun v:V⊕U=> v.elim (fun _ _=>0) (fun i j=>(1:Matrix U U ℝ) i j)) f:= by
   apply DFunLike.congr_fun (F:=(Pce (V⊕U) →ₐ[ℝ] Pce U)) (?_); ext x; cases x <;> simp [aftEval,mixRows,Matrix.one_apply,ite_mul,apply_ite MvPolynomial.C]
end

open Flat Tree
variable {K:KernelChoices}{G:Gauge}{n c:Side}{j t:ℕ} {S:StepData c n}
def upper (F:Forest S.ratio):Matrix (wire G n) (Pine G S F ⊕ wire G c) ℝ:= fun i j=> j.elim ((dropRoot G S F)ᵀ i) (fun _=>0)
lemma upperLives (F:Forest S.ratio)(p:Pap (wire G n)): PowerSeries.coeff 0 (Reef.seat F p)=mixRows (upper F) (PowerSeries.coeff 0 p):= by
    apply orbit_ext; intro x; rw [Reef.seat,attested,mix_eats,PowerSeries.coeff_map]
    change traceP _ (MvPolynomial.rename _ _) = _; unfold traceP; simp_rw [aeval_rename]; congr 2; ext1 v
    unfold Matrix.mulVec dotProduct upper; rw [Fintype.sum_sum_type, Finset.sum_eq_zero (f:=fun i:wire G c => ((Sum.inr i): Pine G S F⊕wire G c).elim _ _*_) (by simp),add_zero]; rfl

variable (P:Flight j t)(L:Lodge P.patch)(h:P.patch.Branches K G)(n:Side)
include h
lemma flagPoint (r:(primary P.patch K n).Choices)(w x:Pap (wire G (n*P.patch.L)))(ρ:ChartRatio G)(H:LocalRatio ρ)(hv:4≤ t)(hp:PowerSeries.coeff 0 w=crunch (kernelP G K.penalty P.wing _)) :
    let F:= Reef.floor K P L n; let S:=primary P.patch K n; let D:=(dropRoot G S F)ᵀ; let T:=pMean G K P n F; let Q:=puppet P h L n
    PowerSeries.coeff 0 (tossed P ρ h L n r w x) = mixRows (D*T) (hearth (D*Q*Dᵀ) (PowerSeries.coeff 0 x)):= by
    intro F S D T Q; let B:= upper (G:=G) F; let N:= ferry P h L n; let A: Matrix _ _ ℝ:=aqua (I:=wire G n) N.saddle
    let C: Matrix (Pine G S F⊕wire G n) (wire G n) ℝ:=fun v:(_⊕_) => v.elim (fun _ _=>0) (fun i j=>(1:Matrix (wire G n) _ ℝ) i j)
    let U:=Bank.outshift P L G K n
    rw [tossed, flag_zero _ _ _ (consolidate P ρ h L n H r w hp hv), Bank.tilt_hull P L h, PowerSeries.coeff_map,upperLives]
    let f:= PowerSeries.coeff 0 x
    change aftEval _ _ (hearth A (mixRows U (mixRows B f)))=_
    rw [mix_budget,hearth_mix]; rw [aft_cores]; change mixRows C _=_; rw [mix_budget];
    have he i v: (B*U) i (.inl v)=D i v:= by
        simp [Matrix.mul_apply,B,U,upper,Bank.outshift,Fintype.sum_sum_type,Matrix.one_apply,mul_ite,D]; rfl
    have hz i v: (B*U) i (.inr v)=(D*T) i v:= by
        rw [Matrix.mul_apply,Fintype.sum_sum_type]; simp only [B,U,Bank.outshift,upper, Matrix.fromBlocks_apply₁₂,Sum.elim_inl,Sum.elim_inr,zero_mul,Finset.sum_const_zero,add_zero];rfl
    have hB : B*U*C=D*T:= by ext i u; rw [Matrix.mul_apply,Fintype.sum_sum_type];simp [he,hz,C,Matrix.one_apply,mul_ite]
    rw [hB]; refine congr_arg (mixRows (D*T)) (?_); rw [show B*U*A*(B*U)ᵀ= D*Q*Dᵀ from ?_];
    ext i v; rw [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.mul_apply];
    have h₁ i (v: Pine G (primary P.patch K n) (floor K P L n)): (B*U*A) i (.inl v)=(D*Q) i v:= by
        rw [Matrix.mul_apply,Fintype.sum_sum_type]; simp_rw [he]; unfold A aqua; simp only [Sum.elim_inl, Sum.elim_inr,mul_zero,Finset.sum_const_zero,add_zero];rfl
    have h₂ i (v:wire G n) : (B*U*A) i (.inr v)=0:= by rw [Matrix.mul_apply,Fintype.sum_sum_type]; simp [A,aqua]
    simp_rw [h₁,h₂]; simp_rw [Matrix.transpose_apply,he,zero_mul, Finset.sum_const_zero,add_zero]; -- cash
end YM.FormalBulk08.Avenue
