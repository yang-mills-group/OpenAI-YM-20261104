import YM.RG02.Flat.Aperture
import YM.RG02.Degree.Rebound

/-!
Analytic localized push outputs through every r on the *same marked table*:
- before and after t-power read and Markov kernel normalization;
- after factoring the vacuum exponential and marking the denominator;
- after cumulant logarithm and normalized division.
Book before `g_{i-1}` resets. The raw leading scalar is NOT a source
coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk
open Filter Function MeasureTheory Set Metric Lattice Wilson RG Precision Tree Supply Bid Marker Extra.Trajectories
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries Profiles
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I : Type}[DecidableEq I][Fintype I]{B : Census I}{c f : Side}{S : StepData c f}

section vac
variable (T : Forest S.ratio) {p : Clip}{R : PathData G}{A : Space G f→ℝ}{m : ℕ}{W : Space G f→ Poly B}
    {η : ChartRatio G} {w : ℝ}{ρ : Dir G c → AxisChart G T}(i : S.Choices)(hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)
variable {σ v Λ : ℝ}(hW : R.Bounds p σ v Λ)(ht : Ink m W)(hh : Ambient A)(hs : S.patch.Branches S.kernel G)(hη : LocalRatio η)(x : Dir G c)

/-- Order supplied by the normalization of the noise. -/
def elevated (S : StepData c f)(G : Gauge): ℕ := by
  let _ := S
  exact Friction.cardinal G* Fintype.card (Edge (Site c))
def unitSeries (S : StepData c f)(η : ChartRatio G) := ((Friction.paidSeries S η)⁻¹)^ Fintype.card (Edge (Site c))

include hη
lemma payments : Near (fun t => (t:ℂ)^elevated S G * ↑(YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G)) (unitSeries S η) := by
   have he := Near.stand (Near.fine_inverse (Friction.restored S η hη) ?_) (Fintype.card (Edge (Site c)))
   swap; · rw [Friction.paid_base S η hη]; apply Complex.ofReal_ne_zero.mpr; exact (mul_pos (Therm.leading_pos ..) hη.scale).ne'
   convert! he using 1
   funext t; unfold elevated YM.RG02.Branch.noisePrefactor
   simp only [Pi.pow_apply,Pi.inv_apply,pow_mul, mul_inv_rev,Complex.ofReal_pow, Complex.ofReal_inv,inv_inv, inv_pow, mul_pow,mul_comm]; simp only [← pow_mul]; rw [Nat.mul_comm (Fintype.card (Edge (Site c)))]

omit hη
include ht
lemma real_base (t : ℝ){p : Clip}{R : PathData G}{A : Space G f→ℝ}(K : ℝ)(U:Set (Config G f)) :
    let a:= (sweep T p R m W A x K t U).part B.quiet; a=Complex.ofReal a.re := by
   intro a
   let z u := Real.exp (-(mainTerm p R u + A (t,u) + t^2* Precision.loop R u)/t^2)
   let L u := S.density (t^2)⁻¹ u (Precision.represent (t • x)) * z u
   have hx u : (Fk.through S p R m W A x t u).part B.quiet= ↑(L u) := by
      have hP : ((((t:ℂ)^m)⁻¹) • W (t,u)).part B.quiet = 0 := by simp [ht.silent]
      change (S.density _ u _ • (z u • (Poly.pass _ : Poly B))).part B.quiet = _
      change ↑(S.density _ u _) * (↑(z u)*(Poly.pass _).part _) = _
      rw [Poly.pass_part _ hP,mul_one,← Complex.ofReal_mul]
   unfold a; rw [sweep,Poly.part_smul]
   rw [show (atSet S p R m W A x t U).part B.quiet= Complex.ofReal (∫ i in U,L i ∂prior G f) from ?_];
   · simp [← Complex.ofReal_inv, Complex.mul_re]
   change (∫ i in U,(Fk.through S p R m W A x t i).part B.quiet ∂prior G f)= _
   simp_rw [hx]; exact integral_ofReal

/-- Inclusive SCRIPT from canonical unmasked perturbation operation.
B projection/input source normalization part of Z. -/
structure Reading (Z : Script B)(K : ℝ)(T : Forest S.ratio)(η : ChartRatio G)
    (U : ℝ→Poly B) : Prop where
  allGraded : Aims (fun t=> (((pref T G K t):ℂ)⁻¹) • U t) Z
  dimensionOnly :
     Aims (fun t=> ((((t:ℂ)^(dim T G))⁻¹ * (t:ℂ)^(elevated S G))) • U t)
       ( Grade.scalar B (C (Complex.ofReal K)*unitSeries S η)* Z)
  actual : ∀ᶠ t in Tested.germ, 0< ((U t).part B.quiet).re ∧ (U t).part B.quiet=(((U t).part B.quiet).re:ℂ)
  vacuum : Near (fun t=> (Real.log (((pref T G K t)⁻¹) * ((U t).part B.quiet).re) : ℂ)) (den (Grade.logarithm Z))
  conditional : Aims (Evaluation.divideAway ∘ U) (Grade.quotient Z)
  connected : Aims (fun t=> Extra.Trajectories.connected (Evaluation.divideAway (U t))) (Grade.logarithm (Grade.quotient Z))

include hp hr h hη
lemma reads {U : ℝ→Poly B}
    (ha : let K:=Draw.multiplier T i hp hr h η x; let Q : ℝ→Poly B:= fun t => (((pref T G K t):ℂ)⁻¹) • U t
          (∀ᶠ t in Tested.germ, (Q t).part B.quiet=(((Q t).part B.quiet).re : ℂ)) ∧ Aims Q (Draw.formal T i hp hr h η x A m W)) :
    let K := Draw.multiplier T i hp hr h η x
    Reading (Draw.formal T i hp hr h η x A m W) K T η U := by
   intro K
   let f := Draw.formal T i hp hr h η x A m W
   let P:= pref T G K
   let V : ℝ→Poly B:= fun t=> ((P t:ℂ)⁻¹) • U t
   obtain ⟨hb,hX⟩:=ha
   change ∀ᶠ t in Tested.germ,(V t).part B.quiet=(((V t).part B.quiet).re : ℂ) at hb
   change Aims V f at hX
   have hu := pref_pays T G K
   have hK : 0<K := Draw.multiplier_pos T i hp hr h η x hη
   have hU : ∀ᶠ t in Tested.germ, 0<P t:= Tested.eventually_pos.mono (fun z hz => hu z hK hz)
   have hx : basepoint f=1 := Draw.configured T i hp hr h η x ht
   have h0 : coeff 0 (den f)=1 := (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans hx
   let L (t:ℝ):= ((V t).part B.quiet).re
   let θ(t:ℝ):= ((U t).part B.quiet).re
   have hN : Near (fun t=>Complex.ofReal (L t)) (den f) := Near.same hX.vac hb
   have hh : ∀ᶠ t in Tested.germ,θ t=P t*L t ∧ L t= (P t)⁻¹ * θ t ∧ (U t).part B.quiet=(θ t:ℂ) := by
       filter_upwards [hU,hb] with t H₁ HE
       have hm := congr_arg (fun v : Poly B=> v.part B.quiet) (show U t= Complex.ofReal (P t) • V t from (smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr H₁.ne') _).symm)
       rw [Poly.part_smul,HE,← Complex.ofReal_mul] at hm
       change (U t).part B.quiet= Complex.ofReal (P t * L t) at hm
       have he' : θ t=P t*L t := congr_arg Complex.re hm
       exact ⟨he', by rw [he',inv_mul_cancel_left₀ H₁.ne'], he'.symm ▸ hm⟩
   have HF : Evaluation.divideAway ∘ U =ᶠ[Tested.germ] Evaluation.divideAway ∘ V := by
      filter_upwards [hU] with t ht
      unfold V; simp only [Function.comp_apply,Evaluation.divideAway, Poly.part_smul]
      rw [mul_inv_rev,inv_inv,smul_smul,mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne'),mul_one]
   refine ⟨hX,?_,?_,?_,(hX.divide (hx.trans_ne one_ne_zero)).same (fun i'=>HF.mono (fun _ z=> congr_arg (fun v : Poly B=> v.part i') z.symm)), (hX.extracted (hx.trans_ne one_ne_zero)).same (fun i'=> HF.mono fun _ he => congr_arg (fun v=> (Extra.Trajectories.connected v).part i') he.symm)⟩
   · let g (t:ℝ) := (t:ℂ)^elevated S G * ↑(YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G)
     have hp := Aims.product (Aims.vacuum (Near.scaled (payments (S:=S) hη) (Complex.ofReal K))) hX
     apply hp.same
     intro i; filter_upwards [Tested.eventually_pos,hU] with t he hi
     change (Poly.bead B ((K:ℂ)*g t)*V t).part i=_
     have hs:= Complex.ofReal_ne_zero.mpr he.ne'
     have hl:= Complex.ofReal_ne_zero.mpr hi.ne'
     rw [Poly.product_bead]; unfold V; rw [smul_smul,← div_eq_mul_inv]; congr 2
     apply (div_eq_iff hl).mpr; unfold P pref g
     push_cast; rw [show (↑K:ℂ) * _= _ from ?_]
     field_simp
   · have hL : Tendsto (fun t=>Complex.ofReal (L t)) Tested.germ (𝓝 1) := by
       have hv := Aspiration.tendsto_first hN; change Tendsto _ _ (𝓝 (coeff 0 _)) at hv
       rwa [h0] at hv
     have hr : Tendsto L Tested.germ (𝓝 1) := by convert (Complex.continuous_re.tendsto (1:ℂ)).comp hL <;> rfl
     filter_upwards [hU, hh,hr.eventually (lt_mem_nhds (show (0:ℝ)<1 by norm_num))] with t ht hv he
     exact ⟨(show 0<θ t from lt_of_lt_of_le (mul_pos ht he) hv.1.ge), hv.2.2⟩
   rw [Draw.vacated T i hp hr h x ht]
   apply Near.same (Asym.real_positive_log hN h0)
   filter_upwards [hh] with t hv; rw [hv.2.1]

variable {Z:Bed}(hY : Comptroller T Z p R)
include hW hh hs hY

/-- Actual unmasked analytic **ray extraction** agreed. Keep V and K costs. -/
theorem attained :
    let K:= Draw.multiplier T i hp hr h η x
    ∃ M∈𝓝 (1:T.Slice G), MeasurableSet M ∧ (∀ u∈M,YM.RG02.Branch.Inspected S (T.drape u)) ∧
     ∀ U∈𝓝 (1:T.Slice G), MeasurableSet U→ U⊆M →
       (∀ᶠ t in Tested.germ,∀ s:B.Mode, IntegrableOn (fun u=> (through S p R m W A x t u).part s) (Profiles.wick T ⁻¹' U) (prior G f)) ∧
       Reading (Draw.formal T i hp hr h η x A m W) K T η (fun t=> atSet S p R m W A x t (Profiles.wick T ⁻¹' U)) := by
    intro K
    obtain ⟨M,hM,hm,HL,H⟩ := focused T i hp hr h hW ht hh hs hη x hY
    refine ⟨M,hM,hm,HL,fun U hu hU he => ?_⟩
    obtain ⟨hk,H⟩:= H U hu hU he
    exact ⟨hk,reads T i hp hr h ht hη x (by
        intro K Q; exact ⟨Filter.Eventually.of_forall fun i=> real_base T ht x i K (wick T ⁻¹' U),H⟩)⟩
end vac
end YM.RG02.Fk
