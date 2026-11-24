import YM.MS.Graphical.IntegratePins
import YM.MS.Graphical.TimesMeasurable

/-!
# The UV limit for multi-mark length sectors, before setting z=0

The lemmas apply again on arbitrary higher forests; the scale-gain persists
irrespective of the polarizations and powers of external momenta. Need only
some positive exponential rate in logarithmic time for holomorphic integration.
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval
variable {I E J : Type} {U : Set ℂ} {p t v a b c R : ℝ} {m n : ℕ} {G : Gauge} {x : Tone.QP} {k j : I→ ℝ} {Y Z : I→ℂ}
variable {F H : Schedule G} {z : ℂ}


lemma negativePlow (hf : Pays R F a) (K : Set ℂ) (HK : IsCompact K) (hK : K ⊆ disc R)
    (hZ : ∀ i, Z i∈ K) (hk : ∀ i, k i≤ b) (hl : ∀ i, k i ≤ j i+c) :
    fell 0 (fun i=>exp (a*k i)) fun i=> plow 0 (-j i) (F (k i) (Z i)) := by
  let f i := plow 0 (-k i) (F (k i) (Z i)); let u i:= k i-j i
  rw [show (fun i=> plow 0 (-j i) (F (k i) (Z i)))=(fun i=> plow 0 (u i) (f i)) from ?_]; swap
  · unfold u f; simp_rw [snow,show ∀ i:I, k i-j i + -k i = - j i from fun i=>by ring]
  intro m E _ _ _ w; have h : ∀ i,u i ≤ c := by intro i; unfold u; specialize hl i; linarith
  have he : (0:ℤ)≤ mass w:= by induction w with| nil=>rfl| cons i w ih=> rw [Price_cons]; exact add_nonneg (by unfold wfield; omega) ih
  let a':ℝ:= mass w; let H:= exp (a'*c);
  have hp : scaleC (0:UScale I) 1 (fun i=>‖amount (0+(mass w:ℂ)) (u i)‖):= by
    refine ⟨H,exp_pos _,0,fun i p _=>?_⟩; simp only [amount,Complex.norm_exp,zero_add,Complex.mul_re,Complex.intCast_im,mul_zero,sub_zero,Complex.ofReal_re,Complex.intCast_re,pow_zero,Pi.one_apply,mul_one];
    unfold H a'; rw [mul_comm (u i)]; gcongr; (first|exact_mod_cast he|exact h i)
  convert! Costs.mul (at_rate (E:=E) hp) (limitF (hf I k Z b hk K HK hK hZ m E w) h) using 1
  · ext i; rw [s_p_vector]
  ext; simp

lemma staysStill (hf : Pays R F a) (K : Set ℂ) (HK : IsCompact K) (hK : K ⊆ disc R)
    (hZ : ∀ i, Z i ∈ K) (hk : ∀ i, k i≤ b) :
    fell 0 (fun i=>exp (a*k i)) fun i=> F (k i) (Z i) := by
  simpa using negativePlow (j:=fun _=>0) hf K HK hK hZ hk (by simpa using hk)

variable (h : Pays R F a) (ha : 0<a) (hf : ∀ t∈ disc R, BorelRow fun s=> F s t)
include h

lemma allDomination (w : Legs (Shore G m)) (t : ℝ) (K : Set ℂ) (HK : IsCompact K) (hK : K ⊆ disc R) :
    ∃ C : ℝ, ∀ z∈K, ∀ s≤t, ‖F s z m w‖ ≤ C * exp (a*s) := by
  obtain ⟨C,hC,k,hk⟩:= ride (staysStill (I:= K×Iic t) (Z:=fun i=>i.1) h K HK hK (fun i=> i.1.property) (k:=fun i=>i.2) (fun i=>i.2.property) m ℝ (ray w)) 0
  exact ⟨ C*(1+‖(1:ℝ)‖)^k, fun z hz s hs=> by simpa only [norm_iteratedFDeriv_zero,Pi.zero_apply,abs_zero,add_zero,one_mul,fieldVal,ray_sail] using hk ((⟨z,hz⟩:K),(⟨s,hs⟩:Iic t)) 1⟩
include ha hf
lemma pinGather (hp : z∈ disc R) (t : ℝ) : Gather (fun v=> F v z) t := by
  intro m l; obtain ⟨C,hC⟩:= allDomination h l t _ (isCompact_singleton (x:=z)) (Set.singleton_subset_iff.mpr hp)
  exact ((integrableOn_exp_mul_Iic ha t).const_mul C).mono' (hf z hp m l).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Iic).mono (fun s hs=> hC _ (by simp) s hs))

/-- Remove UV (iterated on nodes of forest), for all z on the disc and finite
log IR lengths. -/
theorem integral_from_UV (hp : z ∈ disc R) (w : Legs (Shore G m)) (t : ℝ) :
    Tendsto (fun x : ℝ=>∫ i in x..t,F i z m w) atBot (𝓝 (integratePins F t z m w)) :=
  intervalIntegral_tendsto_integral_Iic t (pinGather h ha hf hp t m w) tendsto_id
omit h ha hf

-- translate away the upper endpoint
lemma movedPast (t : ℝ) (f : ℝ → ℂ) : (∫ p in Iic t, f p) = ∫ p in Iic (0:ℝ), f (t+p) := by
  obtain he:= (measurePreserving_add_left volume t).setIntegral_preimage_emb (Homeomorph.addLeft t|>.measurableEmbedding) f (Iic t)
  have hm:(t+ ·) ⁻¹' Iic t=Iic (0:ℝ):= by ext; simp
  rw [hm] at he; exact he.symm

variable (hk : ∀ i, k i ≤ b)
include h ha hf
-- Uniform prices for the recursively integrated schedules.
theorem integrate_pay : Pays R (integratePins F) a := by
  intro I t Z B hv K HK hK hZ
  let J:= I × Iic (0:ℝ); let s : J→ℝ:=fun i=> t i.1+(i.2:ℝ)
  let v : J→ℝ:=fun i=> t i.1; let a' (i:I)(r:ℝ) := plow 0 (-t i) (F (t i+r) (Z i))
  have hs (i:J): s i ≤ v i + 0:= by unfold s v; gcongr; exact i.2.property
  let d : I→ℂ:= fun i=>(exp (-a*t i):ℂ); let g(i:I)(p:ℝ):= d i • a' i p
  obtain hx := negativePlow h K HK hK (Z:=Z∘Prod.fst) (fun i:J=>hZ i.1) (k:=s) (b:=B)
       (fun i=>(hs i).trans (by simpa [v] using hv i.1)) hs
  have hm : scaleC (0:UScale J) (fun i=>exp (-a*v i)) (fun i:J=>‖d i.1‖) :=
    ⟨1,zero_lt_one,0,fun i p _=> by simp [v,d,Complex.norm_exp]⟩
  have hr : fell 0 (fun i:J=>exp (a*i.2)) (fun i:J=> g i.1 i.2) := by
    convert fall_scale (U:=fun i:J=>d i.1) hx hm using 1; swap; · rfl
    ext i; rw [← Real.exp_add]; unfold s v; congr 1; ring
  have hh (i:I) : plow 0 (-t i) (integratePins F (t i) (Z i)) = (d i)⁻¹ • mend (g i) 0 := by
    ext m l; simp_rw [integratePins,g,a', Pi.smul_apply,plow,mend, Pi.smul_apply,smul_eq_mul,integral_const_mul]
    rw [movedPast (t i)]; simp only [plow,integral_const_mul]; field_simp [d]
  simp_rw [hh];
  have ht : fell 0 (fun i:I=>1) (fun i=> mend (g i) 0) := by
    intro m E _ _ _ w; let Q(i:I)(t:ℝ) := fieldVal (g i t m) w
    have hm i p : Measurable fun s:ℝ=> Q i s p:= by
       let z:= Z i
       unfold Q fieldVal g; change Measurable (fun r:ℝ=> d i* ( amount _ (-t i) * F (t i+r) z m _));
       exact ((((hf _ (hK (hZ i)) m _).comp (measurable_const_add (t i))).const_mul _).const_mul _)
    obtain hl : Lawn μ0 Q (fun t=>exp (a*t)):= by
      intro j; obtain ⟨C,hC,b,hb⟩:= ride (hr m E w) j
      exact ⟨C,hC,b,fun i=>(ae_restrict_mem measurableSet_Iic).mono fun t ht p=> by
          simpa only [Q,norm_iteratedFDeriv_zero,Pi.zero_apply,abs_zero,add_zero,one_mul] using hb (i,(⟨t,ht⟩:Iic (0:ℝ))) p⟩
    exact plush (g:=Q) (integrableOn_exp_mul_Iic ha 0) (fun i=>
      (ae_restrict_mem measurableSet_Iic).mono fun t ht=> (hr m E w).smooth (i,(⟨t,ht⟩:Iic (0:ℝ))))
      (fun i p=> (hm i p).aestronglyMeasurable) hl
  have he : scaleC 0 (fun i=> exp (a*t i)) (fun i=> ‖(d i)⁻¹‖) :=
    ⟨1,zero_lt_one,0,fun i p _=> by simp [d,Real.exp_neg,Complex.norm_exp]⟩
  convert fall_scale ht he using 1; ext; simp

omit h ha in
lemma integrate_meas (hp : z∈ disc R) : BorelRow fun t=> integratePins F t z:= by
  -- measurability doesn't even need Gather via translation
  intro m l; let f t:= F t z m l
  change Measurable (fun t=> ∫ i in Iic t,f i); rw [show (fun t=> ∫ i in Iic t,f i)=_ from funext fun t=> movedPast t f]
  have he : Measurable (fun p:ℝ×ℝ=> f (p.1+p.2)):= (hf _ hp m l).comp (measurable_fst.add measurable_snd)
  exact he.stronglyMeasurable.integral_prod_right'.measurable

lemma integrate_hol (hp : ∀ t, Hol (disc R) (F t)) (t : ℝ) : Hol (disc R) (integratePins F t) where
  price c r hr ht := by
    let X:= integratePins F; let U:=closedBall c r
    obtain he:= staysStill (integrate_pay h ha hf) (k:=fun _:U=>t) U (isCompact_closedBall ..) ht (fun i:U=>i.property) (b:=t) (fun _=>le_rfl)
    exact flatRate he _ (exp_pos (a*t)) (fun i=>by rw [mul_one])
  top m l := by
    intro z hz; obtain ⟨R,hR,h⟩:= Arc.radius_pay isOpen_ball hz
    obtain ⟨C,hC⟩:= allDomination ‹Pays _ _ _› l t _ (isCompact_closedBall ..) h
    let A(t:ℂ)(s:ℝ):=F s t m l
    exact (middle (f:=A) isOpen_ball (Eventually.of_forall fun t=> hp t |>.top m l)
       (fun i hi=> (hf _ hi m l).aestronglyMeasurable) hR h
       ((integrableOn_exp_mul_Iic ha t).const_mul C) ((ae_restrict_mem measurableSet_Iic).mono fun i hi z hz=> hC z hz i hi)).differentiableAt
end YM.MS.Graphical
