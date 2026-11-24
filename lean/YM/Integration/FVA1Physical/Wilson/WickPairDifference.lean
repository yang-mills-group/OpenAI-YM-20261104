import YM.Integration.FVA1Physical.Wilson.WickCubeLaw

/-! The two-mark projection includes the incoming two-mark entry and the
covariance of the two singly marked entries. Both are propagated on one
conditional Gaussian, using only bounded-cube errors on their three inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Finset MeasureTheory Comparison.RG02 Comparison.RG02.Valence
open YM.Next.SectorChange
open scoped Classical BigOperators ContDiff
variable {ι:Type} [Fintype ι] [DecidableEq ι]
local notation "V" => (ι→ℝ)

private theorem real_level_integrable (K:Matrix ι ι ℝ) (pd:K.PosDef) {d:ℕ} {f:V→ℝ} (hf:Level d f) :
    Integrable f (Gaussian.cloud K) := by
  have h : f=fun z=>∑ k∈range (d+1),Tensor.diagonal (Tensor.coeff f k 0) z := funext hf.posted
  rw [h];exact integrable_finsetSum _ fun k _=>tensorIntegrable K pd _

theorem finite_level_integrable (K:Matrix ι ι ℝ) (pd:K.PosDef) {d:ℕ} {f:V→ℂ} (hf:Level d f) :
    Integrable f (Gaussian.cloud K) := by
  have re:=real_level_integrable K pd (projected_degree hf Complex.reCLM)
  have im:=real_level_integrable K pd (projected_degree hf Complex.imCLM)
  have h:=(Complex.ofRealCLM.integrable_comp re).add ((Complex.ofRealCLM.integrable_comp im).mul_const Complex.I)
  exact h.congr (.of_forall fun z=>Complex.re_add_im _)

private theorem product_gap (a b c d:ℂ) :
    ‖a*b-c*d‖≤‖a-c‖*‖b‖+‖c‖*‖b-d‖ := by
  rw [show a*b-c*d=(a-c)*b+c*(b-d) by ring]
  exact (norm_add_le ..).trans_eq (by simp only [norm_mul])

variable (K:Matrix ι ι ℝ) (pd:K.PosDef) {C A:ℝ} (hc:0≤C) (rows:∀i,∑ j,|K i j|≤C) (ha:0<A)
local notation "E" f:max => (∫ z:V,f z ∂Gaussian.cloud K)
def pairReadout (K:Matrix ι ι ℝ) (ab a b:V→ℂ) :=
  (∫ z,ab z+a z*b z ∂Gaussian.cloud K)-(∫ z,a z ∂Gaussian.cloud K)*(∫ z,b z ∂Gaussian.cloud K)

include pd hc rows ha
theorem wick_pair_difference (d:ℕ) (ab a b ab' a' b':V→ℂ)
    (dx:Level d ab) (da:Level d a) (db:Level d b) (dx':Level d ab') (da':Level d a') (db':Level d b')
    {δ M:ℝ} (δp:0≤δ) (mp:0≤M)
    (input:∀z,‖z‖≤A→‖ab z-ab' z‖≤δ ∧ ‖a z-a' z‖≤δ ∧ ‖b z-b' z‖≤δ)
    (amplitudes:∀z,‖z‖≤A→‖a z‖≤M ∧ ‖b z‖≤M) :
    let P:=2*cubeWickPrice d C A
    let Q:=2*cubeWickPrice (d+d) C A
    ‖pairReadout K ab a b-pairReadout K ab' a' b'‖≤(P+(Q+P^2)*(2*M+δ))*δ := by
  intro P Q
  have Pp : 0≤P := mul_nonneg (by norm_num) (cubeWick_nonnegative _ hc ha)
  have size(z:V)(hz:‖z‖≤A) : ‖a' z‖≤M+δ := by
    calc ‖a' z‖ = ‖a z+(a' z-a z)‖ := congrArg norm (by ring)
         _ ≤ ‖a z‖+‖a' z-a z‖ := norm_add_le .. 
         _ ≤ M+δ := by rw [norm_sub_rev];exact add_le_add (amplitudes z hz).1 (input z hz).2.1
  have diff (l:ℕ)(f g:V→ℂ)(u:ℝ)(df:Level l f)(dg:Level l g)
      (hit:∀z,‖z‖≤A→‖f z-g z‖≤u) :
      ‖E f - E g‖≤2*cubeWickPrice l C A*u := by
    rw [←integral_sub (finite_level_integrable K pd df) (finite_level_integrable K pd dg)]
    apply complex_wick_cube K pd hc rows ha (n:=l) _ hit
    simpa only [neg_one_mul,sub_eq_add_neg] using df.add (dg.factor (-1))
  have x0:=diff d ab ab' δ dx dx' (fun z hz=>(input z hz).1)
  have x1:‖E a-E a'‖≤P*δ:=diff d a a' δ da da' (fun z hz=>(input z hz).2.1)
  have x2:‖E b-E b'‖≤P*δ:=diff d b b' δ db db' (fun z hz=>(input z hz).2.2)
  have sa : ‖E a'‖ ≤ P*(M+δ) := complex_wick_cube K pd hc rows ha da' size
  have sb : ‖E b‖ ≤ P*M := complex_wick_cube K pd hc rows ha db (fun z hz=>(amplitudes z hz).2)
  have pab : Level ((d+d:ℕ):ℤ) (fun z=>a z*b z) := by simpa only [Nat.cast_add] using da.mul db
  have pab' : Level ((d+d:ℕ):ℤ) (fun z=>a' z*b' z) := by simpa only [Nat.cast_add] using da'.mul db'
  have pi := diff (d+d) (fun z=>a z*b z) (fun z=>a' z*b' z) ((2*M+δ)*δ) pab pab' (fun z hz=>by
    apply (product_gap ..).trans
    have u:=(input z hz).2
    exact (add_le_add (mul_le_mul u.1 (amplitudes z hz).2 (norm_nonneg _) δp)
      (mul_le_mul (size z hz) u.2 (norm_nonneg _) (add_nonneg mp δp))).trans_eq (by ring))
  have cross := (product_gap (E a) (E b) (E a') (E b')).trans
    (add_le_add (mul_le_mul x1 sb (norm_nonneg _) (mul_nonneg Pp δp))
      (mul_le_mul sa x2 (norm_nonneg _) (mul_nonneg Pp (add_nonneg mp δp))))
  unfold pairReadout
  rw [integral_add (finite_level_integrable K pd dx) (finite_level_integrable K pd pab),
      integral_add (finite_level_integrable K pd dx') (finite_level_integrable K pd pab')]
  let S:= ∫ z,a z*b z ∂Gaussian.cloud K
  let T:= ∫ z,a' z*b' z ∂Gaussian.cloud K
  change ‖(E ab + S - E a * E b) - (E ab'+ T - E a' * E b')‖ ≤ _
  rw [show (E ab + S - E a * E b) - (E ab'+ T - E a' * E b') =
      ((E ab-E ab')+(S-T))-(E a* E b-E a'* E b') by ring]
  apply (norm_sub_le ..).trans
  exact (add_le_add ((norm_add_le ..).trans (add_le_add x0 pi)) cross).trans_eq (by dsimp [P,Q];ring)

end YM.Integration.FVA1Physical.Wilson.SignCovariance
