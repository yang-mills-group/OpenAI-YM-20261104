import YangMills.WilsonProof.NativeSupport.NearBonds
import YangMills.WilsonProof.NativeSupport.JointTerminalDirection

/-! The common signed direction in the finite thermal polynomial has
the frozen original picture as its connected derivative. The two local
integrability calculations below are copied from the source-matched
WilsonUniformUnmarkedInletBondCovariances. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointMoments
open Function Finset MeasureTheory Lattice RG Wilson Tree RGComparison.Core16 YM.Pressure
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletConnectedCovariance
open WilsonUniformUnmarkedInletBondCovariances WilsonUniformUnmarkedInletBondRemainder
open scoped Classical BigOperators Topology
variable {G : Gauge} {n c : Side}
private theorem measurableCell (d:Descent n c)(h:d.OK G)(t:d.Tags)(q:sites n d):
    Measurable (fun z:Config G c × Descent.Fields G d=>cell G d t z.1 z.2 q):=by
  induction d with
  | nil=>
    change Measurable fun z:Config G n × Descent.Fields G Descent.nil=>G.price (faceValue z.1 q)
    apply Continuous.measurable
    unfold faceValue
    fun_prop
  | @push m i S T d ih=>
    let D:=Descent.push S T d
    have held:Measurable (fun z:Config G m × Descent.Fields G D=>T.drape (z.2 ∘ Sum.inl)):=
      T.continuous_drape.measurable.comp ((measurable_pi_lambda _ fun _=>measurable_pi_apply _).comp measurable_snd)
    have rest:Measurable (fun z:Config G m × Descent.Fields G D=>z.2 ∘ Sum.inr (α:=T.Free)):=
      (measurable_pi_lambda _ fun _=>measurable_pi_apply _).comp measurable_snd
    rcases q with b|b
    · have signal:Measurable fun z:Config G m × Descent.Fields G D=>S.prediction (T.drape (z.2 ∘ Sum.inl)) t.1 b:=
        (measurable_pi_apply b).comp ((S.prediction_meas h.1 t.1).comp held)
      have coarse:Measurable fun z:Config G m × Descent.Fields G D=>z.1 b:=(measurable_pi_apply b).comp measurable_fst
      exact measurable_const.mul (G.continuous_price.measurable.comp (coarse.mul signal.inv))
    · exact (ih h.2 t.2 b).comp (held.prodMk rest)

theorem cell_envelope (d:Descent n c) (ok:d.OK G) (t:d.Tags) (q:sites n d) :
    Envelope (fun z:Config G c × Descent.Fields G d=>cell G d t z.1 z.2 q) := by
  refine ⟨measurableCell d ok t q,cap d q,?_⟩
  intro z
  have limits:=bounded d t z.1 z.2 q
  simpa only [Real.norm_of_nonneg limits.1] using limits.2

private theorem integrableCell (d:Descent n c)(h:d.OK G)(β:ℕ → ℝ)(t:d.Tags)(V:Config G c){φ:Config G n → ℝ}
    (test:Continuous φ)(q:sites n d):
    Integrable (fun x=>(-cell G d t V x q)*d.integrand β t φ V x) (d.measure G):=by
  have row:=cell_envelope d h t q
  have pair:=row.neg.mul (d.path_envelope h β t φ test)
  have slice:Envelope (fun x=>(-cell G d t V x q)*d.integrand β t φ V x):=by
    refine ⟨pair.meas.comp (measurable_const.prodMk measurable_id),?_⟩
    obtain ⟨C,hh⟩:=pair.cost
    exact ⟨C,fun x=>hh (V,x)⟩
  exact slice.integrable _

theorem entry_center (d : Descent n c) (ok : d.OK G) (β : ℕ→ℝ) (V:Config G c)
    {φ : Config G n → ℝ} (continuous : Continuous φ) (a:ℝ) (q:sites n d) :
    entry d β (fun U => φ U-a) V q=entry d β φ V q-a*entry d β 1 V q := by
  unfold entry
  rw [mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  rw [←integral_const_mul,←integral_sub (integrableCell d ok β t V continuous q)
    ((integrableCell d ok β t V (φ:=1) continuous_const q).const_mul a)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Descent.integrand,Pi.one_apply]
  ring

def moment (d : Descent n c) (Y : ℕ→ℝ) (V:Config G c) (σ:sites n d→ℝ) (φ : Config G n → ℝ) (S:Finset (sites n d)) : ℝ :=
  ∑ t,∫ x,(∏ q∈S,σ q * cell G d t V x q)*d.integrand Y t φ V x ∂d.measure G

theorem empty_moment (d : Descent n c) (Y : ℕ→ℝ) (V:Config G c) (σ:sites n d→ℝ) (φ : Config G n → ℝ) :
    moment d Y V σ φ ∅=mass d Y φ V := by simp [moment,mass]

theorem single_moment (d : Descent n c) (Y : ℕ→ℝ) (V:Config G c) (σ:sites n d→ℝ) (φ : Config G n → ℝ) (q:sites n d) :
    moment d Y V σ φ {q}=-(σ q)*entry d Y φ V q := by
  simp only [moment,entry,prod_singleton,mul_sum]
  apply sum_congr rfl
  intro t _
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

def polynomial {J : Type} (D : Finset J) (m : Finset J→ℝ) (z:ℂ) : ℂ := ∑ S∈D.powerset,z^S.card*(m S : ℂ)

theorem polynomial_zero {J : Type} (D : Finset J) (m : Finset J→ℝ) : polynomial D m 0=(m ∅:ℂ) := by
  unfold polynomial
  rw [sum_eq_single ∅]
  · simp
  · intro T _ hT
    simp [zero_pow (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hT))]
  · simp

theorem polynomial_derivative {J : Type} (D : Finset J) (m : Finset J→ℝ) :
    HasDerivAt (polynomial D m) ((∑ i∈D,m {i}:ℝ):ℂ) 0 := by
  classical
  have each (S:Finset J) : HasDerivAt (fun z : ℂ=>z^S.card*(m S:ℂ)) (if S.card=1 then (m S:ℂ) else 0) 0 := by
    have h:= (hasDerivAt_pow S.card (0:ℂ)).mul_const (m S:ℂ)
    by_cases one : S.card=1
    · simpa [one] using h
    · by_cases zero : S.card=0
      · simpa [zero] using h
      · have pos : S.card-1≠0 := by omega
        simpa [one,zero_pow pos] using h
  have values : ∑ S∈D.powerset,(if S.card=1 then (m S:ℂ) else 0)=((∑ i∈D,m {i}:ℝ):ℂ) := by
    rw [←sum_filter,←powersetCard_eq_filter,powersetCard_one,sum_map,Complex.ofReal_sum]
    rfl
  rw [←values]
  exact HasDerivAt.fun_sum fun i _=>each i

theorem frozen_direction (d : Descent n c) (ok : d.OK G) (β v : ℕ→ℝ) (r:ℝ) (V:Config G c)
    (σ:sites n d→ℝ) {φ:Config G n→ℝ} (smooth : Continuous φ) (invariant : GaugeInvariant φ) :
    let Y:=WilsonUniformUnmarkedInletConnectedShift.temperatures β v r
    let I:=interior d
    HasDerivAt (fun z:ℂ=>polynomial I (moment d Y V σ φ) z/polynomial I (moment d Y V σ 1) z)
      ((-(∑ q∈I,σ q*picture d β v V φ r q):ℝ):ℂ) 0 := by
  intro Y I
  let Z:=mass d Y 1 V
  let F:=mass d Y φ V
  let a:=d.conditioned Y φ V
  let C:=∑ q∈I,σ q*picture d β v V φ r q
  let E (f:Config G n→ℝ):=∑ q∈I,σ q*entry d Y f V q
  have nz : Z≠0 := (positive d ok Y V).ne'
  have aZ : a*Z=F := (eq_div_iff nz).mp (fraction d ok Y V smooth invariant)
  have price (f:Config G n→ℝ) : ∑ q∈I,moment d Y V σ f {q}= -E f := by
    simp only [E,single_moment,neg_mul,sum_neg_distrib]
  have mixed : C*Z=E φ-a*E 1 := by
    simp only [C,E,sum_mul,mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro q _
    change σ q*(entry d Y (fun U=>φ U-a) V q/Z)*Z=_
    rw [entry_center d ok Y V smooth a q]
    field_simp
  have ratio : ((-E φ)*Z-F*(-E 1))/Z^2= -C := by
    apply (div_eq_iff (pow_ne_zero _ nz)).mpr
    nlinarith only [congrArg (fun x:ℝ=>x*Z) mixed,congrArg (fun x:ℝ=>x*E 1) aZ]
  have dZ : polynomial I (moment d Y V σ 1) 0≠0 := by
    rw [polynomial_zero,empty_moment]
    exact Complex.ofReal_ne_zero.mpr nz
  have curve:=(polynomial_derivative I (moment d Y V σ φ)).div (polynomial_derivative I (moment d Y V σ 1)) dZ
  have same : (((-E φ:ℝ):ℂ)*(Z:ℂ)-(F:ℂ)*((-E 1:ℝ):ℂ))/(Z:ℂ)^2=((-C:ℝ):ℂ) := by exact_mod_cast ratio
  simp only [polynomial_zero,empty_moment,price] at curve
  rw [same] at curve
  exact curve

theorem absolute_direction (d : Descent n c) (ok : d.OK G) (β v : ℕ→ℝ) (r:ℝ) (V:Config G c)
    {φ:Config G n→ℝ} (smooth : Continuous φ) (invariant : GaugeInvariant φ) {h:ℝ} (hp:0≤h) :
    let Y:=WilsonUniformUnmarkedInletConnectedShift.temperatures β v r
    let I:=interior d
    let σ q:=if 0≤picture d β v V φ r q then h else -h
    ‖deriv (fun z:ℂ=>polynomial I (moment d Y V σ φ) z/polynomial I (moment d Y V σ 1) z) 0‖ =
      h * ∑ q∈I, |picture d β v V φ r q| := by
  intro Y I σ
  rw [(frozen_direction d ok β v r V σ smooth invariant).deriv,Complex.norm_real,Real.norm_eq_abs,abs_neg]
  have signs (q:sites n d) : σ q*picture d β v V φ r q=h*|picture d β v V φ r q| := by
    unfold σ
    split
    next pos => rw [abs_of_nonneg pos]
    next neg => rw [abs_of_neg (lt_of_not_ge neg),mul_neg,neg_mul]
  simp_rw [signs]
  rw [←mul_sum,abs_of_nonneg (mul_nonneg hp (sum_nonneg fun _ _=>abs_nonneg _))]

end YM.Integration.InletSusceptibility.JointMoments
