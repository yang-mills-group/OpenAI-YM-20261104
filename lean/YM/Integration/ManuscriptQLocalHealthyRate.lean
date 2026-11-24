import YM.Integration.ManuscriptQLocalHealthyOffer

/-! The fixed Wilson-stencil derivative bill has a finite polynomial price
in the genuine schedule. Both the support and the ultraviolet window are
bought before any cutoff, period, marked location or test input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalHealthyRate

open Finset Filter Lattice Wilson RG Marker LocalComparison
open Comparison.Density.RenderM Comparison.Density.RenderM.Token Next.Scheduling
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep Push.AbsoluteSums
open ManuscriptQLocalPacketFootprint
open scoped Classical BigOperators Topology

def coefficient (G : Gauge) (σ : ℝ) (c d k : ℕ) : ℝ :=
  let m := d*k
  let u := Wages.grade c d k
  surcharge σ^m*Real.exp 3*(48:ℝ)^m*((m.factorial:ℝ)^2)*
    ((u.factorial:ℝ)*(4:ℝ)^u)*(∑ t∈range (c+1),2*Wages.startup G t d k)

def supportPower (σ : ℝ) := Nat.ceil ((σ+1)/σ)

theorem support {σ A : ℝ} {o : ℕ} (hσ : 0<σ) (h : Real.exp (σ*o)≤A) :
    Real.exp ((σ+1)*o) ≤ A^supportPower σ := by
  have e : σ+1 ≤ (supportPower σ : ℝ)*σ := (div_le_iff₀ hσ).mp (Nat.le_ceil _)
  calc
    _ ≤ Real.exp ((supportPower σ:ℝ)*(σ*o)) := Real.exp_monotone (by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right e (Nat.cast_nonneg _))
    _ = Real.exp (σ*o)^supportPower σ := Real.exp_nat_mul ..
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le h _

theorem polynomial (G : Gauge) (σ : ℝ) (c : ℕ) (p : BudgetPoint) {ω A : ℝ}
    (hω : 0<ω) (ha : 1≤A) (hB : (p.B:ℝ)≤A) (hw : ω⁻¹≤A) :
    fee G σ p c ω ≤ coefficient G σ c p.power p.order *
      A^(p.power*p.order+Wages.grade c p.power p.order) := by
  let m := p.power*p.order
  let k := Wages.grade c p.power p.order
  have hx : 0≤A := zero_le_one.trans ha
  have hr : (radius ω)⁻¹≤4*A := by
    by_cases h : 1≤ω/4
    · simp only [radius,min_eq_left h,inv_one]
      linarith
    · rw [radius,min_eq_right (le_of_not_ge h),inv_div]
      rw [div_eq_mul_inv]
      linarith
  have h1 : (24*(1+(p.B:ℝ)))^m ≤ (48*A)^m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  have h2 : (radius ω)⁻¹^k≤(4*A)^k := pow_le_pow_left₀
    (inv_nonneg.mpr (le_min zero_le_one (by positivity))) hr k
  have hs : 0≤∑ t∈range (c+1),2*Wages.startup G t p.power p.order :=
    sum_nonneg fun t _=>mul_nonneg (by norm_num) (start_safe (t:=t) p G)
  have hsσ : 0 ≤ surcharge σ := zero_le_one.trans (le_max_left _ _)
  let M := surcharge σ^m*Real.exp 3*((m.factorial:ℝ)^2)*(k.factorial:ℝ)*
    (∑ t∈range (c+1),2*Wages.startup G t p.power p.order)
  have hM : 0≤M := by unfold M;positivity
  calc
    _ = M*((24*(1+(p.B:ℝ)))^m*((radius ω)⁻¹)^k) := by
      unfold fee purchase geometry M
      rw [div_eq_mul_inv,←inv_pow]
      ring
    _ ≤ M*((48*A)^m*(4*A)^k) := mul_le_mul_of_nonneg_left
      (mul_le_mul h1 h2 (pow_nonneg (inv_nonneg.mpr (le_min zero_le_one (by positivity))) k)
        (pow_nonneg (mul_nonneg (by norm_num) hx) m)) hM
    _ = _ := by unfold M coefficient;rw [mul_pow,mul_pow,pow_add];ring

/-- The single threshold in the native schedule pays every finite-power
combination in the Wilson cover, running window, and compensation. -/
theorem absorb {G : Gauge} {V : Type} {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (K r : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ start,∀ m,start ≤ m → ∀N p,m<N →
      let g := Pert.Asymptotics.regulatorRun C N p (m+1)
      0<g → g≤1 → A.admittedCost m^K*g^r≤g^((r:ℝ)-η) := by
  let e := η/(K+1:ℝ)
  obtain ⟨start,h⟩ := A.cost_subpower e (div_pos hη (by positivity))
  refine ⟨start,fun m hm N p hN hg h1=>?_⟩
  let g := Pert.Asymptotics.regulatorRun C N p (m+1)
  have ha := pow_le_pow_left₀ (A.admitted_cost_nonnegative m) (h m hm N p hN) K
  have price : e*(K:ℝ)≤η := by
    have h0 : 0<(K+1:ℝ) := by positivity
    have heq : e*(K+1:ℝ)=η := by unfold e;field_simp
    have he : 0≤e := (div_pos hη h0).le
    linarith only [heq,he]
  calc
    _ ≤ (g^(-e))^K*g^r := mul_le_mul_of_nonneg_right ha (pow_nonneg hg.le _)
    _ = g^((-e)*(K:ℝ)+(r:ℝ)) := by
      rw [←Real.rpow_natCast (g^(-e)) K,←Real.rpow_mul hg.le,←Real.rpow_natCast g r,←Real.rpow_add hg]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hg h1 (by linarith)


/-- Both independently stamped prices grow more slowly than any inverse
coupling power on the same physical trajectory. -/
theorem split {G : Gauge} {V : Type} {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (B : ℕ→ℝ) (hB : ∀ m,0≤B m)
    (cost : ∀ ε : ℝ,0<ε → ∃ i,∀m,i ≤ m → ∀N p,m<N →
      B m ≤ Pert.Asymptotics.regulatorRun C N p (m+1)^(-ε))
    (a b r : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ start,∀ m,start ≤ m → ∀N p,m<N →
      let g := Pert.Asymptotics.regulatorRun C N p (m+1)
      0<g → g≤1 → A.admittedCost m^a*(B m)^b*g^r≤g^((r:ℝ)-η) := by
  let e := η/((a+b:ℕ)+1:ℝ)
  have he : 0<e := div_pos hη (by positivity)
  obtain ⟨i,hi⟩ := A.cost_subpower e he
  obtain ⟨j,hj⟩ := cost e he
  refine ⟨max i j,fun m hm N p hN hg h1=>?_⟩
  let g := Pert.Asymptotics.regulatorRun C N p (m+1)
  have ha := pow_le_pow_left₀ (A.admitted_cost_nonnegative m) (hi m ((le_max_left ..).trans hm) N p hN) a
  have hb := pow_le_pow_left₀ (hB m) (hj m ((le_max_right ..).trans hm) N p hN) b
  have heq : e*((a+b:ℕ)+1:ℝ)=η := by unfold e;field_simp
  have price : e*(a+b:ℕ)≤η := by linarith only [heq,he]
  calc
    _ ≤ ((g^(-e))^a*(g^(-e))^b)*g^r := mul_le_mul_of_nonneg_right
      (mul_le_mul ha hb (pow_nonneg (hB _) _) (pow_nonneg (Real.rpow_nonneg hg.le _) _))
      (pow_nonneg hg.le _)
    _ = g^((-e)*(a+b:ℕ)+(r:ℝ)) := by
      rw [←pow_add,←Real.rpow_natCast (g^(-e)) (a+b),←Real.rpow_mul hg.le,
        ←Real.rpow_natCast g r,←Real.rpow_add hg]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hg h1 (by linarith)

variable {G : Gauge} {V : Type} [DecidableEq V] {C : Family G} {J : Request V}

/-- A single cutoff for all independently marked modes, all periods and
upper cutoffs, and every original physical bank carrying the declared bare
quote. The quote may be the input price or the distinct output geometry. -/
theorem scheduled (hC : C.Makes) (hG : G.Simple) (A : NumericSchedule C J)
    (p : ℕ→BudgetPoint) (width Q : ℕ→ℝ) (d k c r : ℕ) (σ η : ℝ) (hσ : 0<σ) (hη : 0<η)
    (shapes : ∀m,(p m).power=d ∧ (p m).order=k ∧ (p m).supportExponent=σ)
    (cover : ∀m,((p m).B:ℝ)≤A.admittedCost m)
    (widths : ∀m,0<width m ∧ (width m)⁻¹≤A.admittedCost m)
    (units : ∀ m N per,m<N → (p m).threshold≤A.admittedCost m*Pert.Asymptotics.regulatorRun C N per (m+1))
    (Q0 : ∀m,0≤Q m)
    (cost : ∀ ε : ℝ,0<ε → ∃ i,∀m,i ≤ m → ∀N per,m<N →
      Q m ≤ Pert.Asymptotics.regulatorRun C N per (m+1)^(-ε)) :
    ∀ᶠ m : ℕ in atTop,∀ N per,m<N →
      let g := Pert.Asymptotics.regulatorRun C N per (m+1)
      ∀ {n : Side} {Γ : Census V} (P : MarkedPackets J.tests G n Γ) {Y region w} {o : ℕ} {b},
        P.rankCap≤c → Real.exp (σ*o)≤Q m →
        P.Paid (p m) Y region w 1 (width m) (Q m) o b → ∀v,
        SumBudget (ManuscriptQLocalHealthyTariff.contribution (w:=w) P (p m) v g r)
          (coefficient G σ c d k*g^((r:ℝ)-η)) := by
  let j := d*k+Wages.grade c d k
  let u := supportPower σ
  obtain ⟨i,hi⟩ := split A Q Q0 cost (j+c) (u+1) r η hη
  obtain ⟨i0,hi0⟩ := Filter.eventually_atTop.1 (ManuscriptQLocalKernelTariff.small hC hG)
  filter_upwards [Filter.eventually_ge_atTop (max i i0)] with m hm
  intro N per hN g n Γ P Y region w o b hc hcover H v
  have hg := IterationFour.Currency.g_pos hC N per (m+1) hN
  have hg1 := hi0 (m+1) (by omega) N per hN
  let a := A.admittedCost m
  have ha : 1≤a := A.admitted_cost_ge_one m
  have ha0 : 0≤a := zero_le_one.trans ha
  have hfee := polynomial G σ c (p m) (widths m).1 ha (cover m) (widths m).2
  have rate := hi m ((le_max_left ..).trans hm) N per hN hg hg1
  obtain ⟨hp,hk,hs⟩ := shapes m
  rw [hp,hk] at hfee
  have hfee0 : 0≤coefficient G σ c d k := by
    have hstart (s : ℕ) : 0≤Wages.startup G s d k := by rw [←hp,←hk];exact start_safe (t:=s) (p m) G
    have hsum : 0≤∑ t∈range (c+1),2*Wages.startup G t d k := sum_nonneg fun t _=>mul_nonneg (by norm_num) (hstart t)
    have hs0 : 0 ≤ surcharge σ := zero_le_one.trans (le_max_left _ _)
    unfold coefficient
    positivity
  have actual := ManuscriptQLocalHealthyTariff.total P H (p m) rfl
    (show (p m).supportExponent≤2*(p m).supportExponent by linarith [(p m).exponent_pos])
    v r c hc g a hg hg1 ha (units m N per hN)
  rw [hs] at actual
  refine ⟨actual.1,actual.2.1,actual.2.2.trans ?_⟩
  have origin := support hσ hcover
  calc
    _ ≤ (coefficient G σ c d k*a^j*(Q m)^u*g^r*a^c)*Q m := by
      apply mul_le_mul_of_nonneg_right _ (Q0 m)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha0 _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hg.le _)
      exact mul_le_mul hfee origin (Real.exp_pos _).le (mul_nonneg hfee0 (pow_nonneg ha0 _))
    _ = coefficient G σ c d k*((a^(j+c)*(Q m)^(u+1))*g^r) := by
      rw [pow_add,pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left rate hfee0

end YM.Integration.ManuscriptQLocalHealthyRate
end
