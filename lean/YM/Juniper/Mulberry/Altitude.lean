import YM.Juniper.Mulberry.Axis
/-!
 # Gaussian jets for EXP and exact post payload

 At E′ (can be ℝ× E), approximant to norm estimation & output
 derivative Book. This module is the accounting chart + make certificate
 from airmass. Worry about *relative* determinant/tail reserve external.
 Adaptation of `LocalAtlas.Law` log interpolation for mixed engine. Keep
 actuality of `central` number (can differentiate too; radius b) before
 signing anything. Does not assume either Grass or E.C.Modified themselves bounded
 on ALL distribution; only at the CUT. E extension arbitrary beyond unscaled
 book, normalization denominator critical at flat gram. Fuel cost *after L* with
 finite announced D auxiliary size. Price nontrivial moment w.r.t. sweep,
 with all derivatives not expecting CTS from ray choices.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open MeasureTheory Set Function Matrix Metric Filter ProbabilityTheory
open PhysicalNext.Repeat Lantern RG Wilson
open ConnectedActivityE6 Blaze Brush Poll Sienna
open Work.G05 WilsonStartup Analysis Tensor
open LocalAtlas
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {X : Type} [MeasurableSpace X] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        {f:X→ E→ℝ}{D:Set X}{x:E}{b s a q v w t:ℝ}{μ: Measure X}[IsProbabilityMeasure μ]{k n:ℕ}
section rights
-- lower bound on cut: a_min= e^-2 /2 reserved. a=e^-1/2 OK because after scaling buy all combined q cutoff, min pure x and ratio investment. Require C-bill for grace+E, normalized scale. Lower-bound via age q0=0 and thus for sufficiently small d. q measured `Body` from λ before-L.
local notation "Q"=> clump k q w
local notation "X!"=> ball (0:E) b
local notation "F"=> cut μ D f
local notation "u"=> Real.exp 1
noncomputable def ballot (f:X→ E→ℝ)(D:Set X)(x:E) := D.indicator (fun z=> Real.exp (f z x))
local notation "P"=> ballot f D
structure Paint (D : Set X)(k:ℕ)(f:X→ E→ℝ)(b q:ℝ) : Prop where
    awake : 0 ≤ q
    mass : ∀ x:E, ‖x‖<b→Measurable (ballot f D x)
    moon : b ≤ 1
    lunar : q*b ≤ 1
    air z : f z 0=0
    scale (z:X)(x:E) : z∈D → ‖x‖<b → Brush k q 1 (f z) x
variable (p : Paint D k f b q)(hD:MeasurableSet D)(hk:1 ≤ k)
      (h: ∀ y∈Set.Icc (-1:ℝ) 1, Brush k w 1 Real.exp y)
include hk p
omit [FiniteDimensional ℝ E] in
lemma boundsH {z:X}(hx:‖x‖<b) (hz:z∈ D) : |f z x| ≤ 1:= by -- adapt Lantern.amity
   let H:= X!; have ht (x:E) (hx:x∈H):= p.scale z x hz (mem_ball_zero_iff.mp hx); have hi:x∈ H:= mem_ball_zero_iff.mpr hx; have he:= (convex_ball (0:E) b).norm_image_sub_le_of_norm_fderiv_le (fun i h=> ((ht i h).smaller hk).smooth.differentiableAt (by norm_num)) (fun i h=> Eq.trans_le (show ‖fderiv ℝ (f z) i‖=normJ 1 (f z) i from (by rw [Blaze.normJ,norm_iteratedFDeriv_one])) ((Brush.offer.1 (ht i h)).2 1 hk)) (mem_ball_self ((norm_nonneg _).trans_lt hx)) hi; rw [p.air,sub_zero,sub_zero] at he
   exact (he.trans (mul_le_mul_of_nonneg_left hx.le p.awake)).trans p.lunar
include h
omit [FiniteDimensional ℝ E] in
lemma imminent (hx:‖x‖< b) : ∀ z:X, Brush k Q 1 (fun y=> P y z) x:= by
   intro z; by_cases hz:z∈D
   · exact (Lantern.composite (p.scale z x hz hx) (h _ (abs_le.mp (boundsH p hk hx hz)))).shimmy (Eventually.of_forall fun _=> Set.indicator_of_mem hz _)
   have hp :=p.awake; have hw := (h 0 (by simp)).nonneg; have hv:0≤Q:=by unfold clump; positivity
   exact ((Brush.certified (x:=x) (k:=k) zero_le_one (0:ℝ)).climb (by rw [norm_zero]; exact hv) le_rfl).shimmy (Eventually.of_forall fun i=> indicator_of_notMem hz _)
lemma payable (hx:‖x‖<b): Meristem P x μ k ∧ Integrable (P x) μ:=by
    have he:∀ᶠ u' in 𝓝 x, u'∈ X!:= isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)
    obtain ⟨h,hF⟩:= Meristem.points P μ ⟨fun _=>Q,integrable_const _,he.mono fun i hi=> imminent p hk h (mem_ball_zero_iff.mp hi)⟩ (he.mono fun i hi=> p.mass _ (mem_ball_zero_iff.mp hi))
    exact ⟨h,hF.self_of_nhds⟩

lemma market (hx:‖x‖<b): Brush k Q 1 F x := Meristem.buds (payable p hk h hx|>.1) (fun _=>Q) (integrable_const _) zero_le_one (by simp) (Eventually.of_forall (imminent p hk h hx))
local notation "u!"=> (Real.exp (-1)* (1/2:ℝ))
local notation "A"=> ((Real.exp (-1)*(1/2:ℝ))/2)
local notation "Y"=> Set.Icc A (u + A)
include hD
lemma purchases (h' : μ.real Dᶜ ≤ 1/2) (hx : ‖x‖<b) : u! ≤ F x ∧ F x ≤ u:= by
   have hμ: 1/2 ≤ μ.real D:= by rw [measureReal_compl hD,probReal_univ] at h'; linarith only [h']
   have hp {z} (hz:z∈D): f z x ∈ Set.Icc (-1:ℝ) 1:= abs_le.mp (boundsH p hk hx hz)
   have ht:= p.air; have hw : Integrable (P x) μ:= (payable p hk h hx).2
   let V:= P x; unfold cut
   constructor
   · apply le_trans (mul_le_mul_of_nonneg_left hμ (Real.exp_pos _).le)
     rw [show Real.exp (-1)* μ.real D=∫ z, D.indicator (fun _=> Real.exp (-1)) z ∂μ from by rw [integral_indicator hD]; simp; ring]; refine integral_mono ((integrable_const _).indicator hD) hw fun z=>?_
     by_cases hz:z∈D; · change _≤P x z; unfold ballot; simp_rw [indicator_of_mem hz]; exact Real.exp_monotone (hp hz).1
     rw [indicator_of_notMem hz,indicator_of_notMem hz]
   refine le_trans (b:=∫ _z:X,(fun _x:X=>u) _z ∂μ) (a:=∫ z:X,V z ∂μ) (integral_mono hw (integrable_const _) (fun z=>?_)) (le_of_eq (by simp))
   by_cases hz:z∈D; · exact (indicator_of_mem hz (fun z => Real.exp (f z x))).trans_le (Real.exp_monotone (hp hz).2)
   exact (indicator_of_notMem hz _).trans_le (Real.exp_pos _).le

lemma origin (hb:0<b)(i:ℕ)(hi:i ≤ k): Tensor.coeff F i 0 = ∫ z in D, Tensor.coeff (Real.exp ∘ f z) i 0 ∂μ:=by
   have he: Meristem P 0 μ k:= (payable p hk h (show ‖(0:E)‖<b from norm_zero.trans_lt hb)).1
   unfold Tensor.coeff; rw [show iteratedFDeriv ℝ i F 0 = _ from ((he.calls).2 i hi).2,← integral_indicator hD,← integral_smul] -- rw picks which
   refine integral_congr_ae (Eventually.of_forall fun z=>?_)
   by_cases h:z∈D; · rw [Set.indicator_of_mem h]; change _ • iteratedFDeriv ℝ i (fun t=> P t z) 0 = _; rw [show (fun t=>P t z)=(Real.exp ∘ f z) from funext fun t=> Set.indicator_of_mem h _]
   rw [indicator_of_notMem h]; change _ • iteratedFDeriv ℝ i (fun t=> P t z) 0= _; rw [show (fun t=> P t z)=0 from funext fun t=> indicator_of_notMem h _,iteratedFDeriv_zero]; exact smul_zero ..
end rights
section confirm
variable (Y:Measure X) [IsProbabilityMeasure Y] (D:Set X)
    {k n j:ℕ}{f:X→ E→ℝ}
local notation "F!"=> cut Y D f
local notation "Θ"=> (full Y f)
local notation "Z"=> Mulberry.gauge Y f n
local notation "U"=> Real.exp 1
local notation "X*"=> (Real.exp (-1)* (1/2:ℝ))
local notation "X!"=> (X* / 2)
local notation "G'"=> Set.Icc X! (U+X!)
local notation "v'"=> overhead n k *v -- v binder
local notation "Q"=> clump k q w
-- Transport Body integrability assumed from finance. split absolute costs in cigarette. Rental at very high derivatives Vs(m). Tape owner S.B stress.
variable (H : Paint D k f b q)(hD : MeasurableSet D)(h: ∀ y∈ Icc (-1:ℝ) 1, Brush k w 1 Real.exp y)
variable (hn:n+1 ≤ k) (hp : Y.real Dᶜ ≤ 1/2)
    (hZ : cap (full Y f) n v) (hc : cap ( (fun i=> Tensor.coeff (cut Y D f) i 0) - full Y f) n t)
abbrev cost0 (k n:ℕ)(C b d:ℝ) := (C+ LocalAtlas.overhead n k*C)*b^(n+1)+ LocalAtlas.overhead n k*d
local notation "A"=> cost0 k n Q b t
variable (hk: cost0 k n (clump k q w) b t ≤ (Real.exp (-1)*(1/2:ℝ)/2))(he:Treasury k a (Real.exp (-1)*(1/2:ℝ)/2) (Real.exp 1 + Real.exp (-1)*(1/2:ℝ)/2))
local notation "X'"=> clump k v' a
include H h hD hn hp hZ hc hk he
lemma trust (hx:‖x‖<b) : Brush k A b⁻¹ (F! - Z) x ∧ F! x∈G' ∧ Z x∈G' ∧ Brush k X' 1 (Real.log ∘ Z) x:=by
    have hF x (hx': ‖(x:E)‖< b) := market (μ:=Y) H (by omega) h hx'; have hs:=hF x hx; have hK: b>0 := (norm_nonneg _).trans_lt hx; let P:= blockTaylor n (F!)
    have hl : Brush k A b⁻¹ (F! - Z) x:= by
       rw [show F! - Z = (F! - blockTaylor n (F!)) + through n ((fun i=> Tensor.coeff (F!) i 0) - Θ) from ?_]; swap
       · rw [LocalAtlas.through_diff, ← LocalAtlas.daily]; unfold Mulberry.gauge; abel
       exact (LocalAtlas.overall (fun x hx=> hF x (mem_ball_zero_iff.mp hx)) H.moon hn hx).gathering ((LocalAtlas.gross _ hc (hx.le.trans H.moon) k).climb le_rfl ((one_le_inv₀ hK).2 H.moon))
    have hz: |F! x-Z x|≤ X!:= hl.bound.trans hk; have hΘ:= LocalAtlas.fee_sign; have ⟨hc,hp⟩:= purchases H hD (by omega) h hp hx -- order
    have hv : Z x∈ G' := ⟨by linarith only [hc,abs_le.mp hz|>.2],by linarith only [hp,abs_le.mp hz|>.1]⟩
    exact ⟨hl,⟨by linarith only [hΘ,hc],by linarith only [hΘ,hp]⟩,hv,Lantern.composite (LocalAtlas.gross _ hZ (hx.le.trans H.moon) k) (he.log _ hv)⟩
-- runtime RootC finance. export enough for both read.
def esteem (n k:ℕ)(w q v t b a:ℝ) := peg k (cost0 k n (clump k q w) b t) (clump k q w) (LocalAtlas.overhead n k * v) a + (clump k (LocalAtlas.overhead n k*v) a + LocalAtlas.overhead n k * clump k (LocalAtlas.overhead n k*v) a)*b^(n+1)
lemma rides (hx:‖x‖<b):
   Brush k (esteem n k w q v t b a) b⁻¹ (sampleLog Y D f - Mulberry.clean Y f n) x ∧ Brush k (clump k (clump k q w) a) 1 (sampleLog Y D f) x:=by
    obtain ⟨hl,hF,hP,hY⟩:= trust Y D H hD h hn hp hZ hc hk he hx
    have hs: Brush k (clump k q w) 1 F! x:= market H (by omega) h hx
    let g:=sampleLog Y D f; let z:= Real.log ∘ through n (full Y f)
    refine ⟨?_, Lantern.composite hs (he.log _ hF)⟩
    apply ((LocalAtlas.log_variation he LocalAtlas.fee_sign hs (LocalAtlas.gross _ hZ (hx.le.trans H.moon) k) hF hP ((one_le_inv₀ ((norm_nonneg _).trans_lt hx)).mpr H.moon) hl).gathering (LocalAtlas.overall (f:=z) (fun x hx=> (trust Y D H hD h hn hp hZ hc hk he (mem_ball_zero_iff.mp hx)).2.2.2) H.moon hn hx)).shimmy
    exact Eventually.of_forall fun i=> by change g i - _=g i-z i+(z i-_); unfold Mulberry.clean; ring
end confirm
end YM.Juniper.Mulberry
