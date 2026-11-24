import YM.Integration.WilsonThermometerMixedAmplitude
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedGallery
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push Push.Corrected Push.AbsoluteSums
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached RG3.Letters MeasureTheory Comparison.RG02.Order
open WilsonThermometerMixedAmplitude
open scoped Classical BigOperators
variable {R:Marker.Census (Fin 3)} {G:Gauge} {n:Side} {P:Rep G n} {o:Fin 3→Site n}
  {X ι:Type*} {p:BudgetPoint} {F:ℕ→ForcedAddress G n} {K:Code G n} {q T:ℂ}

/-- Select address and mode before the tests. The factor is exactly one on all proper singletons. -/
def rent (c:ℂ)(use:R.Mode→Prop)(s:R.Mode):ℂ:=if 1<s.val.card ∧ use s then c else 1

def paint (c:ℂ)(use:R.Mode→Prop)(z:Poly R):Poly R:=Poly.inject fun s=>rent c use s*z.part s

theorem amplitude (use:R.Mode→Prop)(p:Poly R)(inv:q*T=1):
    Line q (paint 0 use p) p (paint T use p):=by
  constructor
  · intro s small
    change rent T use s*p.part s-rent 0 use s*p.part s=0
    simp [rent,not_lt_of_ge small]
  · ext1 s
    change p.part s=rent 0 use s*p.part s+q*(rent T use s*p.part s-rent 0 use s*p.part s)
    by_cases active:1<s.val.card ∧ use s
    · simp [rent,active,←mul_assoc,inv]
    · simp [rent,active]

def lamps (c:ℂ)(use:ι→R.Mode→Prop)(A:Lamps X ι G p o R):Lamps X ι G p o R:={ A with
  nominal:=fun x i=>rent c (use i) (A.mode i) • A.nominal x i
  legal:=fun x i=>Next.Foundations.regular_smul _ (A.legal x i)
  pure:=fun x i U sunny=>congrArg (fun y:ℂ=>rent c (use i) (A.mode i)*y) (A.pure x i U sunny) }

def hard (c:ℂ)(use:ℕ→R.Mode→Prop)(A:Hard X p F K o R):Hard X p F K o R where
  hard x i U:=paint c (use i) (A.hard x i U)
  locality x i:=by
    refine ⟨fun t U=>congrArg (paint c (use i)) ((A.locality x i).gauge t U),?_,
      fun U V h e=>congrArg (paint c (use i)) ((A.locality x i).reads U V h e),?_⟩
    · have cont:Continuous (paint c (use i)):=continuous_pi (fun s=>continuous_const.mul (Poly.get s).continuous)
      exact cont.measurable.comp (A.locality x i).borel
    · intro U s live
      apply (A.locality x i).carry U s
      intro hg
      exact live (by change rent c (use i) s*(A.hard x i U).part s=0;rw [hg,mul_zero])
  charged x i U live:=by
    apply A.charged x i U
    intro hg
    apply live
    ext1 s
    change rent c (use i) s*(A.hard x i U).part s=0
    rw [hg,Poly.part_nil,mul_zero]
  quiet x i U:=by
    change rent c (use i) R.quiet*(A.hard x i U).part R.quiet=_
    rw [show rent c (use i) R.quiet=1 by simp [rent,Marker.Census.quiet],one_mul,A.quiet]

def gallery (c:ℂ)(reg:ι→R.Mode→Prop)(forced:ℕ→R.Mode→Prop)(A:Gallery X ι o P R):
    Gallery X ι o P R:=⟨lamps c reg A.E,hard c forced A.K⟩

theorem sheet (c:ℂ)(use:ι→R.Mode→Prop)(A:Lamps X ι G p o R)(x:X)(U:Config G n)(i:ι):
    (lamps c use A).frame i x U=paint c (use i) (A.frame i x U):=by
  have light:(lamps c use A).light x i U=rent c (use i) (A.mode i)*A.light x i U:=by
    by_cases sunny:A.clear i
    · simp [Lamps.light,lamps,sunny]
    · simp only [Lamps.light,lamps,if_neg sunny]
      change masked p.threshold (A.ground i) _ U=rent c (use i) (A.mode i)*masked p.threshold (A.ground i) _ U
      by_cases healthy:Healthy p.threshold (A.ground i) U
      · rw [masked_eq _ _ _ _ healthy,masked_eq _ _ _ _ healthy]
        rfl
      · rw [masked_ne _ _ _ _ healthy,masked_ne _ _ _ _ healthy,mul_zero]
  ext1 s
  change (Poly.send (A.mode i) ((lamps c use A).light x i U)).part s =
    rent c (use i) s*(Poly.send (A.mode i) (A.light x i U)).part s
  simp only [Poly.part_send,light]
  split
  next h=>rw [h]
  next=>rw [mul_zero]

/-- The whole signed input on the actual disjoint hard covers and the unchanged common Wilson divisor. -/
theorem field (A:Gallery X ι o P R)(reg:ι→R.Mode→Prop)(forced:ℕ→R.Mode→Prop)
    (inv:q*T=1){w:Fin 3→ℝ}(hw:∀i,0<w i){e₀ k₀ eT kT:ℝ}
    (lo:(gallery 0 reg forced A).Pays w P.p.supportExponent e₀ k₀)
    (hi:(gallery T reg forced A).Pays w P.p.supportExponent eT kT)(x:X)(U:Config G n):
    Line q ((gallery 0 reg forced A).density x U) (A.density x U) ((gallery T reg forced A).density x U):=by
  apply scaled
  apply WilsonThermometerMixedAmplitude.product
  · apply WilsonThermometerMixedAmplitude.passed
    apply series _ _ _ (lo.budget.sums P.p.exponent_pos.le hw x U) (hi.budget.sums P.p.exponent_pos.le hw x U)
    intro i
    change Line q ((lamps 0 reg A.E).frame i x U) (A.E.frame i x U) ((lamps T reg A.E).frame i x U)
    rw [sheet,sheet]
    exact amplitude _ _ inv
  · apply series _ _ _ (Hard.packet_summing _ lo.wages P.p.exponent_pos.le hw x U)
      (Hard.packet_summing _ hi.wages P.p.exponent_pos.le hw x U)
    intro cover
    by_cases admitted:P.activities.admissible P.p U cover
    · simp only [packet,if_pos admitted]
      exact products cover _ _ _ (fun i _=>amplitude (forced i) (A.K.hard x i U) inv)
    · simp only [packet,if_neg admitted]
      exact same _

/-- Integrate all seven faces first, with the same mass, and then retain the whole connected logarithm. -/
theorem older {Y:Type*}[MeasurableSpace Y](μ:Measure Y)(mass:ℂ)(A K F:Y→Poly R)
    (origin:∀y,Line q (A y) (K y) (F y))
    (base:∀s,Integrable (fun y=>(A y).part s) μ)
    (raised:∀s,Integrable (fun y=>(F y).part s) μ):
    Line q (WilsonOriginalSignedHardHearing.mean μ mass A) (WilsonOriginalSignedHardHearing.mean μ mass K)
      (WilsonOriginalSignedHardHearing.mean μ mass F):=by
  apply scaled
  constructor
  · intro s small
    change (∫ x,(F x).part s ∂μ)-(∫ x,(A x).part s ∂μ)=0
    rw [←integral_sub (raised s) (base s)]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall (fun x=>(origin x).marked s small)
  · ext1 s
    change (∫ x,(K x).part s ∂μ)=(∫ x,(A x).part s ∂μ)+q*((∫ x,(F x).part s ∂μ)-(∫ x,(A x).part s ∂μ))
    let d:Y→ℂ:=fun x=>(F x).part s-(A x).part s
    have hd:Integrable d μ:=(raised s).sub (base s)
    calc
      _ = ∫ x,(A x).part s+q*d x ∂μ:=by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x=>congrArg (fun p:Poly R=>p.part s) (origin x).value)
      _ = _:=by
        rw [integral_add (base s) (hd.const_mul q),integral_const_mul]
        exact congrArg (fun z=>(∫ x,(A x).part s ∂μ)+q*z) (integral_sub (raised s) (base s))

end YM.Integration.WilsonThermometerMixedGallery
