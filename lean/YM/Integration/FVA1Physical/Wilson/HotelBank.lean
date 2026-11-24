import YM.Integration.FVA1Physical.Wilson.OrbitCollar
import YM.Integration.FVA1Physical.Wilson.RoughFieldValue
import YM.Integration.FVA1Physical.Wilson.HotelTest

/-! Sharp removal of the physically sampled single collar from the independent
mixed Wilson stencil. The uncut side is in the actual parent forest gauge.
Only a single local failure event occurs, at every admitted volume. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH
open Push.Uniform MSbar.Midpoint MSbar.Bakery.Film MSbar.Bakery MSbar.Measuring
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι]

theorem hotel_bank_mean (G:Gauge) (m s p:ℕ) (Q:ℝ) :
    ∀ᶠ y:ℝ in atTop,∀ (A:Issue G) (J:ι→Lamp G) (χ:ChartRatio G) (part:Bool) (o:ι→Site A.f)
      (b:Site A.c), |A.fClock⁻¹| ≤ 4*y → |A.fClock| ≤ 1 →
      BankPaid b y s p m 1 (emittedRows A χ (jointFieldBank J A o part) p) →
      ∀ {c:Side} (S:StepData c A.c) (R:Rep G A.c) (O:Config G c){σ C δ Λ w:ℝ},Admitted O R S σ C δ Λ w →
      ∀ (F:Forest S.ratio) (V:Voice G) (μ:Positions (Key F G)),Clear G V → pillow y ≤ room y →
      let live:=hotel F (boxX y b) (boxY y b) V O μ (pillow y) (room y)
      let copy:=chambers F (boxY y b) V O μ
      let P:=independentStencil J A χ p o part
      let E:=expect S R O
      ∀ rare:ℝ,chance S R O liveᶜ ≤ rare →
      |E (live.indicator (P ∘ copy))-E (P ∘ canoe (S:=S) F)| ≤
        (p+1:ℕ)*y^(-Q) + y^(m+3)*rare := by
  let r:=(LocalH.geom_patch G).choose
  have r0:0 ≤ r:=(LocalH.geom_patch G).choose_spec.1.le
  let constant:=(p+1:ℕ)*(1+4*r)^(m+1)
  filter_upwards [bank_exterior_words G m s p 1 Q (C:=4) (by norm_num),eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop constant] with y ticket y1 large
  intro A J χ part o b clock small bank c S R O σ C δ Λ w adm F V μ clear pad live copy P E rare tail
  have y0:0 ≤ y:=zero_le_one.trans y1
  have a0:0 ≤ αm y:=zpow_nonneg (sq_nonneg _) _
  let X:=boxX y b
  let Y:=boxY y b
  have xy:X ⊆ Y:=halo_subset ..
  have measurableLive:MeasurableSet live:=(garden_main F X Y V O μ clear xy).from_here
  have measurableCopy:Measurable copy:=(informed F X Y V O μ clear xy).1
  have cont:Measurable P:=independentStencil_meas J A χ p o part
  have tmp:1+|A.fClock⁻¹| *r ≤ (1+4*r)*y:=by
    nlinarith only [mul_le_mul_of_nonneg_right clock r0,y1]
  have bound(W): |P W| ≤ y^(m+3) := by
    have cert:=independentStencil_global J A χ b o part a0 small bank W
    rw [Real.rpow_one] at cert
    calc |P W| ≤ (p+1:ℕ)*(y*(1+|A.fClock⁻¹| *r)^(m+1)) := cert
         _ ≤ (p+1:ℕ)*(y*((1+4*r)*y)^(m+1)) := by gcongr
         _ = constant*y^(m+2) := by simp only [constant,mul_pow,pow_succ];ring
         _ ≤ y*y^(m+2) := mul_le_mul_of_nonneg_right large (pow_nonneg y0 _)
         _ = y^(m+3) := by ring
  let U : Config G A.c → Config G A.c := Heath.canoe (S:=S) F
  let cut:=live.indicator (P ∘ U)
  have cutbound:Envelope cut:=Envelope.piece measurableLive
    ⟨cont.comp (canoe_cont F).measurable,y^(m+3),fun W=>bound _⟩ (Envelope.const 0)
  have near(W:Config G A.c)(h:W∈live) : |P (copy W)-P (U W)| ≤ (p+1:ℕ)*y^(-Q) := by
    let T:=emittedRows A χ (jointFieldBank J A o part) p
    have same(e:Edge (Site A.c))(he:e.1∈X) : U W e=copy W e := by
      apply cognizant F X Y V O μ clear xy h pad e (xy he)
      apply (halo_spec ..).mpr
      exact ⟨e.1,he,(Work.E01.sep_step_le e.1 e.2).trans (by omega)⟩
    have word(i:ℕ)(hi:i≤p):
        |MvPolynomial.eval (chartLog A.fClock (copy W)) (PowerSeries.coeff i T)-
         MvPolynomial.eval (chartLog A.fClock (U W)) (PowerSeries.coeff i T)| ≤ y^(-Q) := by
      have paid:=ticket A.c b T bank i hi A.fClock clock 0 (fun _=>U W) (fun _=>copy W) (fun _=>same)
      exact (le_mul_of_one_le_left (abs_nonneg _) (w_start (div_nonneg a0 zero_le_two) s _)).trans paid
    change |(∑ i∈range (p+1),A.fClock^i*MvPolynomial.eval (chartLog A.fClock (copy W)) (PowerSeries.coeff i T))-
      (∑ i∈range (p+1),A.fClock^i*MvPolynomial.eval (chartLog A.fClock (U W)) (PowerSeries.coeff i T))| ≤ _
    rw [←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑ _∈range (p+1),y^(-Q) := by
           apply sum_le_sum;intro i hi
           rw [←mul_sub,abs_mul,abs_pow]
           exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) small) (word i (Nat.le_of_lt_succ (mem_range.mp hi)))
             (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
         _ = _ := by simp
  have first:|E (live.indicator (P ∘ copy))-E cut| ≤ (p+1:ℕ)*y^(-Q) := by
    apply expect_difference adm ((cont.comp measurableCopy).indicator measurableLive) cutbound
    intro W;by_cases h:W∈live
    · simpa only [cut,Set.indicator_of_mem h,Function.comp_apply] using near W h
    simpa only [cut,Set.indicator_of_notMem h,sub_self,abs_zero] using
      (mul_nonneg (Nat.cast_nonneg (p+1)) (Real.rpow_nonneg y0 (-Q)))
  have second:=expect_on_chart O measurableLive adm (P ∘ U) (cont.comp (canoe_cont F).measurable)
    (pow_nonneg y0 (m+3)) (fun W=>bound _) tail
  exact (abs_sub_le _ (E cut) _).trans (add_le_add first ((abs_sub_comm _ _).le.trans second))

end YM.Integration.FVA1Physical.Wilson
