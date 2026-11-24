import YM.AllOrder.Laplace.Helix
/-! # Full log after aggregating jointly weighted cylindrical coefficients -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested MeasureTheory ProbabilityTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical
open Matrix Lattice ConnectedActivityE6 Blaze Brush Poll PhysicalNext Repeat Lantern Local Vote PositionX.Jet
open scoped BigOperators MatrixOrder
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {ι:Type} [Fintype ι][DecidableEq ι]
local notation "Y"=> Body ι
variable {A B:X×Poll.Body ι→ℝ}{m:X→Matrix ι ι ℝ}{ρ:X→Poll.Body ι}
    (h:Accent A B m ρ) (R:ℝ)
local notation "F"=> (A ∘ Prod.snd)
set_option quotPrecheck false
local notation "Hi"=> fun p : ℝ×(X×Y)=> R*Real.exp (-B p.2)
local notation "μ"=> sweep (m 0)⁻¹
variable (v:X)(r:ℝ)(hr:0< Laplace.curvature A (fderiv ℝ (course v) 0 1) (fderiv ℝ (ρ ∘ course v) 0 1)+r)
local notation "Y₀"=> ρ ∘ course v
local notation "Q"=> prepare F (course v) Y₀ r
local notation "Ψ"=> (Hi) ∘ tone (course v) Y₀
local notation "T"=> slopeP (course v) A B m ρ
local notation "φ"=> glowP (course v) A B m ρ
local notation "S"=> Real.exp ∘ T
local notation "α"=> Real.exp (-r)* R* munit (m 0)
local notation "J"=> Shield.lens₀ (m 0)⁻¹
def wholeP (A B:X×Poll.Body ι→ℝ)(m:X→Matrix ι ι ℝ)(ρ:X→Poll.Body ι)(v:X)(n:ℕ):= Tensor.diagonal (Vote.moment A B ρ m n) (1,v)
local notation "ξ"=> wholeP A B m ρ v
include h
lemma citation (z:Y) (i:ℕ): someJ (φ z) i=(i.factorial:ℝ)⁻¹ * Tensor.diagonal (Vote.probe A B ρ m i z) (1,v) := by rw [show φ z=(fun t:ℝ => (Real.exp ∘ grace A B ρ m z) (t • (1,v))) from (funext fun i=> by simp [glowP,course,smul_eq_mul])]; exact jet_entry (h:=Real.exp ∘ grace A B ρ m z) (n:=i) ((grace_nice h z i).exp) (1,v) -- path equality
-- W height cc precondition on positive of θ kept from true T
variable {c:ℝ}(he:∀ z:ι→ℝ,dotProduct z ((m 0)⁻¹ *ᵥ z) ≤ c*dotProduct z z)
include he
lemma aggregate (n:ℕ): Integrable (fun z => someJ (φ z) n) μ ∧ ∫ z,someJ (φ z) n ∂μ=ξ n:= by
 obtain ⟨u,w,p,ha⟩:= hollow h n; obtain ⟨C,-,hE⟩:= Brush.compact (k:=n) isCompact_Icc (f:=Real.exp) (s:=Icc 0 2) fun i _=> Real.contDiff_exp.contDiffAt
 have hv:=(raw_h ha le_rfl he (p:=p) (k:=n) (show _ ≤(Fintype.card ι:ℝ) from le_rfl) (hE 0 (by norm_num)) le_rfl).1
 let E:= ContinuousMultilinearMap.apply ℝ (fun i:Fin n=>ℝ×X) ℝ (fun _=>(1,v)); simp_rw [citation h v]; constructor
 · exact (E.integrable_comp hv).const_mul _
 unfold wholeP Vote.moment Vote.raw Tensor.diagonal; rw [_root_.smul_apply, ContinuousMultilinearMap.integral_apply hv, integral_const_mul]; rfl
include hr
lemma summation : part volume Q Ψ = α • plus (someJ S) (ξ):= by
   funext k; let G z:= plus (someJ S) (someJ (φ z)) k
   unfold part; simp_rw [show ∀ z:Y,normTerm Ψ Q k (onLane z)= α * (J z * G z) from (fun i=> (congr_fun (mint h R v i r hr) k).trans (mul_assoc ..)), integral_const_mul]
   rw [← Shield.recommends (m 0)⁻¹ h.station.self_of_nhds.1.inv G]; apply congr_arg (α * ·)
   unfold G plus Tested.conv Tested.term; simp_rw [PowerSeries.coeff_mul,PowerSeries.coeff_mk]; rw [integral_finsetSum]; swap; · exact fun i _ => (aggregate h v he i.2).1.const_mul _
   simp_rw [integral_const_mul,(aggregate h v he _).2]
omit h he hr in
lemma whole_at0 : ξ 0=1 := by unfold wholeP; rw [Vote.moment0] -- implicit
include R in
lemma stage (hR:0<R) : SigmaP.logS (Real.exp r • part volume Q Ψ)=just (Real.log (R*munit (m 0))) + someJ T + logS ξ:= by
   have ht := nice_slope h _ (course_claim h v).cont (course_claim h v).p0; let s:=plus (someJ S) ξ; have hS :0< someJ S 0:=by rw [someJ_zero]; exact Real.exp_pos _
   have hw:0<ξ 0:=by rw [whole_at0]; norm_num
   have hs':0<s 0:=by simpa [s,plus,Tested.conv,Tested.term,PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.constantCoeff_mk] using mul_pos hS hw
   have hs:0<R*munit (m 0):= mul_pos hR (munit_pos (m 0))
   rw [summation h R v r hr he, smul_smul, show Real.exp r * α=R*munit (m 0) from (by rw [Real.exp_neg, ← mul_assoc (Real.exp r), mul_inv_cancel_left₀ (Real.exp_pos r).ne']),← exact_scale, log_mash (show 0<just _ 0 from hs) hs',log_const _ hs,log_mash hS hw, conviction ht,log_expS,add_assoc]
end YM.AllOrder.Laplace.SigmaP
