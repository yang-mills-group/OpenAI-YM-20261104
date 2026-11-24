import YM.RG01.Kernel.Play
/-! # Ambient affine noise score exactly on physical matrix displacements

Pairs are forward/adjoint displacements relative to each coarse base
edge. Use independent complex variables in these slots; take the actual
conjugate only under pullback to real coarse data. Thus no illegal
analytification of the real trace/Re or indicator is needed. Charts and
weights use the scale eps per incident altered edge; summing eps is here
needed for *probability*-norm transport (not an unforced log price on the
representation: needs separate localized/anchored supply, or spend the
explicit supported sum). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Kernel
open Function Filter Set MeasureTheory Complex Metric Topology Finset Matrix Lattice RG Wilson
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
abbrev Block (G:Gauge):= Fin G.repDim→ Fin G.repDim→ℂ
abbrev Pair (G:Gauge):= Block G×Block G
abbrev Angles (G : Gauge)(n:Lattice.Side):= Edge (Site n)→Pair G
variable {G:Gauge}

-- one scale currency. Mat to array conversion deliberately budget as fixed G cost.
def array (m:G.Mat):Block G:=m
lemma height (G:Gauge):∃ C:ℝ,1≤C∧∀ u:G.El,‖array (G.mat u)‖ ≤ C:=by
  have he : Continuous (fun u:G.El=> array (G.mat u)) := by -- Pi topology
    apply continuous_pi; intro i; apply continuous_pi; intro j; unfold array; fun_prop (disch:=aesop)
  obtain ⟨M,hM⟩:= (isCompact_range he.norm).bddAbove
  exact ⟨max 1 M,le_max_left ..,fun i=> (hM ⟨i,rfl⟩).trans (le_max_right ..)⟩
def tariff (G:Gauge):ℝ:= (height G).choose * (G.repDim:ℝ)^2
lemma fee (G:Gauge) : 1 ≤ tariff G:=by unfold tariff; refine one_le_mul_of_one_le_of_one_le (height G).choose_spec.1 (one_le_pow₀ (by exact_mod_cast G.dimPos))

def score (u : G.El)(A:Pair G):ℂ:= ((Matrix.of A.1*G.mat u).trace + (G.mat u⁻¹*Matrix.of A.2).trace)/(2*(G.repDim:ℂ))
private lemma oneBound (u:G.El)(A:Block G): ‖trace (Matrix.of A * G.mat u)‖ ≤ tariff G*‖A‖:=by
  let D:= (height G).choose; let d:ℝ:=G.repDim
  have hU:‖array (G.mat u)‖≤D:=(height G).choose_spec.2 _
  unfold Matrix.trace; simp_rw [Matrix.diag_apply,Matrix.mul_apply,Matrix.of_apply]
  apply le_trans (norm_sum_le ..)
  apply le_trans (Finset.sum_le_sum (s:=univ) (g:=fun _=>d* (‖A‖*D)) (fun i _=> (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (s:=univ) (g:=fun _=> ‖A‖*D) ?_) (by simp [d])))) (by simp [tariff,d,D]; ring_nf; exact le_rfl)
  intro j _
  rw [norm_mul]
  exact mul_le_mul ((norm_le_pi_norm _ _).trans (norm_le_pi_norm A _)) ((show ‖G.mat u j i‖ ≤ ‖array (G.mat u)‖ from (norm_le_pi_norm (array (G.mat u) j) _).trans (norm_le_pi_norm (array (G.mat u)) _)).trans hU) (norm_nonneg _) (norm_nonneg _)
lemma score_norm (u:G.El)(A:Pair G): ‖score u A‖≤tariff G * ‖A‖:=by
  have he:1≤(G.repDim:ℝ):=by exact_mod_cast G.dimPos
  let t:=tariff G
  have ht:0 ≤ t:= zero_le_one.trans (fee G)
  have hA:‖trace (Matrix.of A.1*G.mat u)‖≤t*‖A‖:=(oneBound ..).trans (mul_le_mul_of_nonneg_left (norm_fst_le A) ht)
  have hB:‖trace (G.mat u⁻¹*Matrix.of A.2)‖≤t*‖A‖:=by rw [Matrix.trace_mul_comm]; exact (oneBound ..).trans (mul_le_mul_of_nonneg_left (norm_snd_le A) ht)
  unfold score; rw [norm_div,norm_mul,Complex.norm_natCast, RCLike.norm_ofNat]
  apply (div_le_iff₀ (by positivity)).2; change _≤ (t*‖A‖)*_
  apply le_trans (norm_add_le ..); nlinarith [mul_nonneg ht (norm_nonneg A)]

lemma inserted (u:G.El)(M:G.Mat):score u (array M,array (star M))=(↑((M*G.mat u).trace.re / (G.repDim:ℝ)):ℂ):=by
  unfold score
  dsimp only [Prod.fst,Prod.snd,array]
  have h:trace (G.mat u⁻¹ * star M)=star (trace (M*G.mat u)):= by rw [G.mat_inv,← star_mul,Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose]
  change ((trace (M*G.mat u)+trace (G.mat u⁻¹ * star M))/_) = _
  rw [h]; push_cast
  rw [Complex.star_def,Complex.re_eq_add_conj]; field_simp

lemma score_add (u:G.El)(A B:Pair G): score u (A+B) = score u A+score u B:=by
    have ha(X Y:Block G): Matrix.of (X+Y)=(Matrix.of X + Matrix.of Y: G.Mat):=rfl
    simp only [score,Prod.fst_add,Prod.snd_add,ha,add_mul,mul_add,trace_add]; ring
lemma score_money (u:G.El)(A:Pair G)(v:ℂ): score u (v•A) = v*score u A := by
    have ha(X:Block G): Matrix.of (v•X)=(v•Matrix.of X: G.Mat):=rfl
    unfold score; change ((Matrix.of (v • A.1)*_).trace+(_*Matrix.of (v • A.2)).trace)/_=_
    rw [ha,ha, Matrix.smul_mul,Matrix.mul_smul,trace_smul,trace_smul]; simp only [smul_eq_mul]; ring
/-- Complex steering map of a literal noise row. -/
def script {c f:Lattice.Side}(S:StepData c f)(β:ℝ)(eps:Edge (Site c)→ℝ)(V:Config G c)(t:S.Choices)(U:Config G f)(M:Angles G c):ℂ:=
  (β*S.kernel.penalty:ℝ)*∑ i,(eps i:ℂ)*score (V i*(S.prediction U t i)⁻¹) (M i)

def channel {c f:Lattice.Side}(S:StepData c f)(β:ℝ)(eps:Edge (Site c)→ℝ)(V:Config G c)(t:S.Choices)(U:Config G f): Angles G c →L[ℂ]ℂ:=
  LinearMap.toContinuousLinearMap {
    toFun:=script S β eps V t U
    map_add' := by intro M N; unfold script; rw [← mul_add _ _ (∑ _,_), ← sum_add_distrib]; simp only [Pi.add_apply,score_add,mul_add]
    map_smul' := by intro a M; unfold script; change _=a*(_*_); rw [mul_left_comm]; apply congr_arg; rw [mul_sum]; apply sum_congr rfl; intro i _; simp only [Pi.smul_apply,score_money]; ring }

variable {c f:Lattice.Side}(S:StepData c f)(β:ℝ)(eps:Edge (Site c)→ℝ)(V:Config G c)
    (t:S.Choices)

lemma score_measurable (A:Pair G) (i:Edge (Site c))(h:S.patch.Branches S.kernel G): Measurable
    (fun (U:Config G f)=> score (V i*(S.prediction U t i)⁻¹) A) :=by
  apply (Continuous.measurable (show Continuous (fun u:G.El=> score u A) by unfold score; unfold Matrix.trace Matrix.diag; fun_prop)).comp
    ((measurable_const).mul (((measurable_pi_apply i).comp (S.prediction_meas h t)).inv))
lemma booked (h:S.patch.Branches S.kernel G)(he:∀ i,0 ≤ eps i):
    Wheel (Wilson.prior G f) (channel S β eps V) ( |β*S.kernel.penalty| *tariff G*(∑ i,eps i)):= by
  have hp:0 ≤ tariff G:=zero_le_one.trans (fee G)
  refine ⟨by positivity [Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>he i)], fun i U=> ContinuousLinearMap.opNorm_le_bound _ (by positivity [Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>he i)]) fun m=> ?_,fun i m=> (show Measurable _ from ?_).aestronglyMeasurable⟩
  · change ‖script S β eps V i U m‖ ≤ _
    unfold script; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (abs_nonneg _)).trans
    have ht (j:Edge (Site c)): ‖(eps j:ℂ)*score (V j*(S.prediction U i j)⁻¹) (m j)‖ ≤ eps j*(tariff G*‖m‖):=by
      rw [norm_mul,Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg (he _)]
      exact mul_le_mul_of_nonneg_left ((score_norm ..).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm m j) hp)) (he j)
    apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>ht j)) (abs_nonneg _)).trans
    rw [← Finset.sum_mul]; ring_nf; exact le_rfl
  change Measurable (fun U=> script S β eps V i U m)
  unfold script; exact measurable_const.mul (Finset.measurable_fun_sum _ fun j _=> measurable_const.mul (score_measurable _ _ _ (m j) j h))

/-- Pull back independent displacement variables to the real group fields.
Zero weights permit exact localization. -/
def encoded (V':Config G c): Angles G c:= fun i=>
    let A:= G.mat (V' i*(V i)⁻¹)-1
    (eps i)⁻¹ • (array A,array (star A))
lemma noiseReal (V':Config G c) (h:∀ i,eps i=0→V' i=V i) (U:Config G f) :
    Complex.exp (script S β eps V t U (encoded eps V V'))*(S.noise β (S.prediction U t) V:ℝ)= ↑(S.noise β (S.prediction U t) V'):=by
  let Q:=S.prediction U t; let r i:= V i*(Q i)⁻¹; let r' i:= V' i*(Q i)⁻¹
  let b:=β*S.kernel.penalty
  have he(i): (eps i:ℂ)* score (r i) (encoded eps V V' i) = ↑(G.price (r i)-G.price (r' i)):=by
    by_cases he:eps i=0
    · simp [he,r,r',h i he]
    let A:=G.mat (V' i*(V i)⁻¹)-1
    have hh:trace (A*G.mat (r i))=trace (G.mat (r' i))-trace (G.mat (r i)):=by
      unfold A r r'
      rw [sub_mul,one_mul,trace_sub,← G.mat_mul]
      group
    have hf : encoded eps V V' i = ((eps i:ℂ)⁻¹) • (array A,array (star A)):=by
      unfold encoded A; ext <;> simp [Complex.ofReal_inv]
    rw [hf,score_money,inserted,hh,Complex.sub_re]
    unfold Gauge.price; push_cast; field_simp [he]; ring
  unfold script; change Complex.exp (_*∑ i,(eps i:ℂ)* score (r i) _) * _ = _
  simp_rw [he, mul_sum, ← Complex.ofReal_mul, Complex.exp_sum,← Complex.ofReal_exp]
  norm_cast -- change goal to reals
  unfold StepData.noise StepData.penaltyWeight
  rw [← Finset.prod_mul_distrib]; refine prod_congr rfl fun i _=> ?_
  change Real.exp ((β*S.kernel.penalty)*(G.price (r i)-G.price (r' i)))*(_*Real.exp (-β*S.kernel.penalty*G.price (r i)))=_
  rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
end YM.RG01.Kernel
