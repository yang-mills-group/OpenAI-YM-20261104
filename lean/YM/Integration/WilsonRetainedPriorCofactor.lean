import YM.Integration.WilsonRetainedPriorAperture
import YM.Integration.WilsonPhysicalHistoryRetainedIntegral

/-! Correlated square-integrable readings of the true physical change of an
incoming vacuum molecule, including its original failed-flag probability. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open scoped Topology BigOperators Classical ENNReal
variable {G : Gauge}

private theorem restricted_pair {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    {E : Set Ω} (he : MeasurableSet E) {q : ℝ} (hq : 0≤q) {A : Ω→ℝ}
    (am : AEStronglyMeasurable A ν) (cap : ∀z,|A z|≤E.indicator (fun _=>q) z)
    (h : Ω→ℂ) (hm : AEStronglyMeasurable h ν) (h2 : Integrable (fun z=>‖h z‖^2) ν) :
    Integrable (fun z=>h z*(A z:ℂ)) ν ∧
    ‖∫z,h z*(A z:ℂ) ∂ν‖ ≤ Real.sqrt (∫z,‖h z‖^2 ∂ν)*Real.sqrt (ν.real E)*q := by
  let b:=E.indicator (fun _=>(1:ℝ))
  have nn : (0:Ω→ℝ)≤ᵐ[ν] b := ae_of_all _ fun z=>by
    by_cases hz:z∈E <;> simp [b,hz]
  have first : MemLp (fun z=>‖h z‖) 2 ν := (memLp_two_iff_integrable_sq hm.norm).2 h2
  have second : MemLp b 2 ν := (memLp_const (1:ℝ)).indicator he
  have two : ENNReal.ofReal 2=2 := by norm_num
  have holder:=integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (show (0:Ω→ℝ)≤ᵐ[ν] fun z=>‖h z‖ from ae_of_all _ fun _=>norm_nonneg _) nn
    (by rwa [two]) (by rwa [two])
  have square (z) : b z^2=b z := by by_cases hz:z∈E <;> simp [b,hz]
  have integral : ∫z,b z^2 ∂ν = ν.real E := by
    simp_rw [square]
    exact integral_indicator_one he
  have cs : (∫z,‖h z‖*b z ∂ν)≤Real.sqrt (∫z,‖h z‖^2 ∂ν)*Real.sqrt (ν.real E) := by
    simpa [Real.rpow_two,Real.sqrt_eq_rpow,integral] using holder
  have major : Integrable (fun z=>(‖h z‖*b z)*q) ν := (first.integrable_mul second).mul_const q
  have dominated (z) : ‖h z*(A z:ℂ)‖≤(‖h z‖*b z)*q := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine (cap z).trans_eq ?_
    by_cases hz:z∈E <;> simp [b,hz]
  have typed := major.mono' (hm.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable am)) (ae_of_all _ dominated)
  refine ⟨typed,(norm_integral_le_integral_norm _).trans ((integral_mono typed.norm major dominated).trans ?_)⟩
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right cs hq

theorem molecule_correlated (R : Run G) {N n j d : ℕ} (hj : j<N) (A : Comparison R (p:=n) hj d) :
    let P:=R.family.path.rep N n j
    let Q:=approximation R (p:=n) hj d
    let δ:=(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1)
    ∃ b : ℕ→ℝ, (∀ x,SumBudget (fun i=>if (P.activities.reg i).site=x then
      P.p.mass (P.activities.reg i).support (b i) else 0) δ) ∧
      ∀ {c L : Side} {S : StepData c (R.family.side j n)} {T : Tube G S} {F : Forest S.ratio}
        {W μ C x : ℝ} {M : Teller G} {D : ConnectedActivityE6.Target G M} {o : Target.Order G W}
        (H : Cash W x μ L D o C T P) (X : Coat T F),
        X.x=x → X.width=o.K → X.manifest → δ≤1 →
        (∀ (Y : F.Slice G) (l : Finset ℕ) (z : Air (R.family.side j n) G) (i : ℕ),
          |(X.wrapY Y).vertex P D.table W o.a l D.halo z (regularHead S i)|≤1/4) →
        ∀ (l : Finset ℕ) (p : Molecule S),
        let err:=fun v : Head S=>(5/2:ℝ)*regularFee S b v
        let bill:=insertedCost (fun v=>H.fair v+err v) err p.toList
        let gap:=fun u=>X.body P D.table W o.a l D.halo p u-X.body Q D.table W o.a l D.halo p u
        let ν:=(F.order G).prod X.dice
        ∀(f : F.Slice G × Air (R.family.side j n) G→ℂ),AEStronglyMeasurable f ν →
          Integrable (fun u=>‖f u‖^2) ν →
          Integrable (fun u=>f u*(gap u:ℂ)) ν ∧
          ‖∫u,f u*(gap u:ℂ) ∂ν‖≤Real.sqrt (∫u,‖f u‖^2 ∂ν)*Real.sqrt (H.alarms^(blaze p).card)*bill := by
  intro P Q δ
  obtain ⟨b,price,paid⟩:=molecule_aperture R hj A
  refine ⟨b,price,?_⟩
  intro c L S T F W μ C x M D o H X ht hy hp small quarter l p err bill gap ν f fm fi
  let J:=X.catastrophe o.ξ P.beta (blaze p)
  let E : Set (F.Slice G × Air (R.family.side j n) G):=Prod.snd ⁻¹' J
  obtain ⟨hm,alarm,non,cap⟩:=paid H X ht hy hp small quarter l p
  have em : MeasurableSet E := hm.preimage measurable_snd
  have ea : ν.real E=X.dice.real J := by
    have e : E=Set.univ ×ˢ J := by ext z; simp [E]
    simp [ν,e,Measure.real,Measure.prod_prod]
  have gm : AEStronglyMeasurable gap ν :=
    ((H.integrated X ht hy hp l p).sub (retained_integrable R hj A H X ht hy hp small l p).2).aestronglyMeasurable
  have changed (z) : |gap z|≤E.indicator (fun _=>bill) z := by
    calc
      _ ≤ J.indicator (fun _=>bill) z.2 := cap z
      _ = _ := by by_cases hz:z.2∈J <;> simp [E,hz]
  have h:=restricted_pair em non gm changed f fm fi
  refine ⟨h.1,h.2.trans ?_⟩
  rw [ea]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt alarm)
    (Real.sqrt_nonneg _)) non

end YM.Integration.OriginalMarkedRunAction
