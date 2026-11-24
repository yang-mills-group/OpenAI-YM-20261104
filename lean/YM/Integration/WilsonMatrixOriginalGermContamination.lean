import YM.Integration.WilsonMatrixOriginalGermOccupancy
import YM.Integration.WilsonRegisteredRegularQuota

/-! Price the complete forced part of a two-field connected read in its original Wilson law.
Each linear term contains one rough rent. The joint term contains the two rents on the
same configuration and the product of the two separately centered means. -/
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermContamination
open MeasureTheory Lattice Wilson RG Source MergeProof PhysicalNext.Repeat.Legato
open WilsonInheritedRegisteredField WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermOccupancy
open WilsonRegisteredRegularQuota
open Trace.Physical.GermGraph Next.Rank.Price
open private marked swap from YM.Integration.WilsonMatrixOriginalGermGram
open scoped Classical

private def tariff {X:Type*} [MeasurableSpace X] (μ:Measure X) (a b:X→ℝ):ℝ:=
  (∫x,a x*b x ∂μ)+(∫x,a x ∂μ)*(∫x,b x ∂μ)

private theorem bill {X:Type*} [MeasurableSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    {f g:X→ℂ} {a b:X→ℝ} (hf:Envelope f) (hg:Envelope g) (ha:Envelope a) (hb:Envelope b)
    (fa:∀x,‖f x‖ ≤ a x) (gb:∀x,‖g x‖ ≤ b x):‖moment μ f g‖ ≤ tariff μ a b:=by
  have one {F:X→ℂ} {A:X→ℝ} (hF:Envelope F) (hA:Envelope A) (bound:∀x,‖F x‖ ≤ A x):
      ‖∫x,F x ∂μ‖ ≤ ∫x,A x ∂μ:=(norm_integral_le_integral_norm F).trans
    (integral_mono (hF.integrableC μ).norm (hA.integrable μ) bound)
  have prod (x:X):‖f x*g x‖ ≤ a x*b x:=by
    rw [norm_mul];exact mul_le_mul (fa x) (gb x) (norm_nonneg _) ((norm_nonneg _).trans (fa x))
  apply (norm_sub_le ..).trans
  rw [norm_mul]
  exact add_le_add (one (hf.mulC hg) (ha.mul hb) prod) (mul_le_mul (one hf ha fa) (one hg hb gb)
    (norm_nonneg _) ((norm_nonneg _).trans (one hf ha fa)))

private theorem add_left {X:Type*} [MeasurableSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    {f g h:X→ℂ} (hf:Envelope f) (hg:Envelope g) (hh:Envelope h):
    moment μ (fun x=>f x+g x) h=moment μ f h+moment μ g h:=by
  unfold WilsonMatrixOriginalGermGram.moment;simp_rw [add_mul]
  rw [integral_add ((hf.mulC hh).integrableC μ) ((hg.mulC hh).integrableC μ),integral_add (hf.integrableC μ) (hg.integrableC μ)]
  ring

private theorem add_right {X:Type*} [MeasurableSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    {f g h:X→ℂ} (hf:Envelope f) (hg:Envelope g) (hh:Envelope h):
    moment μ f (fun x=>g x+h x)=moment μ f g+moment μ f h:=by
  rw [swap μ f _,add_left μ hg hh hf,swap μ g f,swap μ h f]

private theorem scale {X:Type*} [MeasurableSpace X] (μ:Measure X) (u v:ℝ) (a b:X→ℝ):
    tariff μ (fun x=>u*a x) (fun x=>v*b x)=u*v*tariff μ a b:=by
  have eq (x:X):u*a x*(v*b x)=u*v*(a x*b x):=by ring
  unfold tariff;simp only [eq,integral_const_mul];ring

private theorem single {X:Type*} [MeasurableSpace X] (μ:Measure X) [IsProbabilityMeasure μ] (b:X→ℝ):
    tariff μ (fun _=>1) b=2*∫x,b x ∂μ ∧ tariff μ b (fun _=>1)=2*∫x,b x ∂μ:=by
  unfold tariff;simp [two_mul]


private theorem pair {X:Type*} [MeasurableSpace X] (ν:Measure X) [IsProbabilityMeasure ν]
    {f g u v:X→ℂ} {h k:X→ℝ} (a s B₀ B₁:ℝ) (fr:Envelope f) (gr:Envelope g)
    (ur:Envelope u) (vr:Envelope v) (eh:Envelope h) (ek:Envelope k)
    (F:∀x,‖f x‖ ≤ 3*a*B₀*1) (G:∀x,‖g x‖ ≤ 3*a*B₁*1)
    (U:∀x,‖u x‖ ≤ s*a*B₀*h x) (V:∀x,‖v x‖ ≤ s*a*B₁*k x):
    ‖moment ν (fun x=>f x+u x) (fun x=>g x+v x)-moment ν f g‖ ≤
      a^2*B₀*B₁*(6*s*((∫x,h x ∂ν)+(∫x,k x ∂ν))+s^2*tariff ν h k):=by
  have fv:=bill ν fr vr ((Envelope.const (3*a*B₀)).mul (Envelope.const 1)) ((Envelope.const (s*a*B₁)).mul ek) F V
  have ug:=bill ν ur gr ((Envelope.const (s*a*B₀)).mul eh) ((Envelope.const (3*a*B₁)).mul (Envelope.const 1)) U G
  have uv:=bill ν ur vr ((Envelope.const (s*a*B₀)).mul eh) ((Envelope.const (s*a*B₁)).mul ek) U V
  rw [add_left ν fr ur (gr.addC vr),add_right ν fr gr vr,add_right ν ur gr vr]
  rw [show moment ν f g+moment ν f v+(moment ν u g+moment ν u v)-moment ν f g=
      moment ν f v+moment ν u g+moment ν u v by ring]
  apply (norm_add_le ..).trans
  apply (add_le_add (norm_add_le ..) (le_refl _)).trans
  apply (add_le_add (add_le_add fv ug) uv).trans
  rw [scale,scale,scale,(single ν k).1,(single ν h).2]
  exact le_of_eq (by ring)

variable {G:Gauge} (R:Run G) {m N p:ℕ}

theorem paid (age:R.family.ref 4 ≤ m) (interior:m<N) (w z:R.family.label 4)
    (o t:Site (R.family.side m p)) (B₀ B₁:ℝ)
    (pre₀:Next.UVStress.quota R.family 4 m N p w ≤ R.family.S.a m^4*B₀)
    (pre₁:Next.UVStress.quota R.family 4 m N p z ≤ R.family.S.a m^4*B₁):
    let ν:=OPE.Therm.scene R.family.path N p m
    let h:=rent R m N p o
    let k:=rent R m N p t
    let σ:=safety R.family m
    ‖moment ν (field R.makes interior.le w o) (field R.makes interior.le z t)-
      moment ν (regular R.makes interior.le w o) (regular R.makes interior.le z t)‖ ≤ 
        stock R.family m^2*B₀*B₁*(6*σ*((∫x,h x ∂ν)+(∫x,k x ∂ν))+
          σ^2*((∫x,h x*k x ∂ν)+(∫x,h x ∂ν)*(∫x,k x ∂ν))):=by
  let ν:=OPE.Therm.scene R.family.path N p m
  letI:IsProbabilityMeasure ν:=OPE.Therm.probability (H:=R.family.path) (p:=p) R.makes.wilson interior.le
  let h:=rent R m N p o
  let k:=rent R m N p t
  let a:=stock R.family m
  let s:=safety R.family m
  let f:=regular R.makes interior.le w o
  let g:=regular R.makes interior.le z t
  let u:=forced R.makes interior.le w o
  let v:=forced R.makes interior.le z t
  have fr:Envelope f:=regular_envelope R.makes interior.le age w o
  have gr:Envelope g:=regular_envelope R.makes interior.le age z t
  have ur:Envelope u:=marked R age interior.le w o
  have vr:Envelope v:=marked R age interior.le z t
  have eh:Envelope h:=bounded R interior o
  have ek:Envelope k:=bounded R interior t
  have reg_bound (y:R.family.label 4) (o':Site (R.family.side m p)) (B:ℝ)
      (eq:Next.UVStress.quota R.family 4 m N p y ≤ R.family.S.a m^4*B):
      ∀x,‖regular R.makes interior.le y o' x‖ ≤ 3*a*B*1:=by
    intro x
    have pr:=WilsonRegisteredRegularQuota.original R.makes interior.le age y o' x
    have ca:0<R.family.S.a m^4:=pow_pos (R.family.S.a_pos m) _
    have cash:=mul_le_mul_of_nonneg_left eq (inv_pos.mpr ca).le
    rw [←mul_assoc,inv_mul_cancel₀ ca.ne',one_mul] at cash
    rw [mul_one];apply pr.trans;apply mul_le_mul_of_nonneg_left cash
    exact mul_nonneg (by norm_num) (zero_le_one.trans (R.family.path.levels.params m).columns_ge)
  have U (x):‖u x‖ ≤ s*a*B₀*h x:=by
    rw [mul_comm];exact WilsonMatrixOriginalGermForeground.on_run R age interior.le w B₀ pre₀ o x
  have V (x):‖v x‖ ≤ s*a*B₁*k x:=by
    rw [mul_comm];exact WilsonMatrixOriginalGermForeground.on_run R age interior.le z B₁ pre₁ t x
  have e₀:(field R.makes interior.le w o)=(fun x=>f x+u x):=funext (separated R.makes interior.le w o)
  have e₁:(field R.makes interior.le z t)=(fun x=>g x+v x):=funext (separated R.makes interior.le z t)
  change ‖moment ν _ _-moment ν f g‖ ≤ a^2*B₀*B₁*(6*s*((∫x,h x ∂ν)+(∫x,k x ∂ν))+s^2*tariff ν h k)
  rw [e₀,e₁]
  exact pair ν a s B₀ B₁ fr gr ur vr eh ek (reg_bound w o B₀ pre₀) (reg_bound z t B₁ pre₁) U V

end YM.Integration.WilsonMatrixOriginalGermContamination
