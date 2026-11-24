import YM.XSpace.Sweeper
/-!
# Calibrated coupling jet on regulators independent from exact Wilson trajectory
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Filter Set MeasureTheory Trace Graph3 Maxwell Maxwell.Free Photo Cirrus Normalize Chiral Structure1 AxesTangent PowerSeries ComplexConjugate Retirement Lattice
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(W:Initialize G) {V:Normalize.Store G}(Y:Rose.Pick V)(g:G.Simple)(l: Mesh)
abbrev inversion := rescale (-1:ℂ)
lemma parity₁ (x:Sample 3)(χ:Badge)(H:V.Meets W x.F 6): inversion (batchT (cooked W V 6 x) χ)= if 0∈χ then -batchT (cooked W V 6 x) χ else batchT (cooked W V 6 x) χ:=by
  apply PowerSeries.ext; intro i; let V':=cooked W V 6 x i; let q:= missing (tag G) χ; let f:=batchT (cooked W V 6 x) χ; rw [inversion,coeff_rescale,batchT,coeff_mk]; -- batchT maybe RHS unfolds
  have hv: ((-1:ℂ)^i)*V' q=V' (hinge 6 ∘ q):=by rw [show V' (hinge 6 ∘ q)=_ from cooksV W V 6 x _ _ H]; simp [Complex.real_smul]; rfl
  split_ifs with h; rw [hv,bud χ h V']; simp only [map_neg, coeff_mk]; rfl
  rw [hv,show hinge 6 ∘ q = q from begin χ h,coeff_mk]
lemma parity₂ (x:Sample 3)(H: V.Meets W x.F 6): inversion (together W V x)= -together W V x:=by
  unfold together b3; simp only [two_smul,map_sub,map_add,map_mul, parity₁ W x _ H]; simp; ring
-- sampling at every bare period with center rule
variable {l}
def test := coerce Y.image
@[simp] lemma tests (x: Points 3): test Y x= (Y.image x:ℂ):=rfl
lemma casts_complem : inverted (test Y)=test Y:=by ext1 x; change star (↑(Y.image x):ℂ)=(↑(Y.image x):ℂ); exact Complex.conj_ofReal _
variable (l)
def Detector : PS:= PowerSeries.mk (fun i=> Deposit l (fun x=>coeff i (together W V x)) (test Y))
lemma detector (i:ℕ): coeff i (Detector W Y l)= Deposit l (fun x=> coeff i (together W V x)) (test Y):=coeff_mk ..
private lemma real_view (x:Fin 3→Cover): star (l.smear x (test Y))= l.smear x (test Y):=by rw [←coil,casts_complem]
lemma full_real (i:ℕ): star (coeff i (Detector W Y l))= coeff i (Detector W Y l):=by rw [detector,Deposit]; simp only [star_mul,star_sum,real_view,real_pt,star_pow,show star (↑l.spacing:ℂ)=_ from Complex.conj_ofReal l.spacing]; rw [mul_comm (Finset.sum ..)]; refine congr_arg (_*·) (Finset.sum_congr rfl (fun x hx => mul_comm .. ))
lemma prepared_odd (H:V.Meets W l 6): inversion (Detector W Y l)= -Detector W Y l:=by
  apply PowerSeries.ext; intro i; rw [inversion,coeff_rescale,map_neg,detector]; have he(x):= parity₂ (V:=V) W (⟨l,x,0⟩:Sample 3) H; unfold Deposit; let c : ℂ:= (-1)^i; have hp(x): c* coeff i (together W V (⟨l,x,0⟩:Sample 3))= -coeff i (together W V (⟨l,x,0⟩:Sample 3)):=by rw [← map_neg, ← he]; exact (coeff_rescale ..).symm
  rw [mul_left_comm c, ← mul_neg, ← Finset.sum_neg_distrib, Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun y _=>?_ ; rw [mul_left_comm c, hp, mul_neg]
lemma odds (H:V.Meets W l 6): coeff 0 (Detector W Y l)=0:=by
  have h:=congr_arg (coeff 0) (prepared_odd W Y l H); rw [inversion, coeff_rescale,pow_zero,one_mul,map_neg] at h; linear_combination h/2
abbrev c_T:= cT Y.cut G Y.image
include g in
lemma diagnosed : Tendsto (fun i=> coeff 1 (Detector W Y i)) Front (𝓝 (↑(c_T Y):ℂ)):=by
  have he:= sees_test (conf 3) (test Y) _ (conf_open _) (scanFirst W V g) (fun _ _ _=>rfl) (test Y).tsupport_subset; rw [show (test Y).applyTo _=(c_T Y:ℂ) from ?_] at he; simpa only [detector] using he
  unfold Test.applyTo c_T cT; rw [← integral_complex_ofReal]; refine integral_congr_ae (Eventually.of_forall fun x=>?_); simp only [tests]; by_cases hx:x∈ tsupport Y.image; rw [on_stage W g V Y.grants Y.manages (Y.segment hx).1]; exact (Complex.ofReal_mul ..).symm; simp only [image_eq_zero_of_notMem_tsupport hx,Complex.ofReal_zero,zero_mul]
-- T subtract g=0 then divide. Complex power series convenient

def chosen : PS := ((↑(c_T Y):ℂ)⁻¹) • (Detector W Y l - PowerSeries.C (coeff 0 (Detector W Y l)))
lemma zero_choice : constantCoeff (chosen W Y l)=0:=by rw [chosen,← coeff_zero_eq_constantCoeff_apply,_root_.map_smul,_root_.map_sub, coeff_C,if_pos rfl]; simp
lemma puts (e:ℕ)(he:e≠0): coeff e (chosen W Y l)= (↑(c_T Y):ℂ)⁻¹*coeff e (Detector W Y l):=by rw [chosen,map_smul,map_sub,coeff_C,if_neg he,sub_zero];rfl
lemma real_c (i:ℕ): star (coeff i (chosen W Y l))=coeff i (chosen W Y l):=by by_cases h:i=0; simp [h,coeff_zero_eq_constantCoeff_apply,zero_choice]; rw [puts W Y l i h, star_mul,full_real,star_inv₀, show star (↑(c_T Y):ℂ)=_ from Complex.conj_ofReal (c_T Y),mul_comm]
lemma odd_c (H:V.Meets W l 6): inversion (chosen W Y l)= -chosen W Y l:=by apply PowerSeries.ext; intro i; rw [inversion,coeff_rescale,map_neg]; by_cases h:i=0; simp [h, coeff_zero_eq_constantCoeff_apply,zero_choice]; rw [puts W Y l i h,mul_left_comm]; rw [← coeff_rescale]; rw [prepared_odd W Y l H]; simp
include g in
lemma xc : Tendsto (fun i=> coeff 1 (chosen W Y i)) Front (𝓝 1):=by
  simp_rw [puts W Y _ 1 (by decide)]; have hh: (c_T Y : ℂ)≠0:= Complex.ofReal_ne_zero.mpr Y.fresh.ne; exact inv_mul_cancel₀ hh ▸ ((diagnosed W Y g).const_mul (↑(c_T Y):ℂ)⁻¹)
include g in
theorem usable : ∀ᶠ l: Mesh in Front, coeff 1 (chosen W Y l)≠0:= (xc W Y g).eventually (eventually_ne_nhds one_ne_zero)
end YM.XSpace.Rose
