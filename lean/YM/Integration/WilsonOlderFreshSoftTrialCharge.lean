import YM.Integration.WilsonOlderFreshSoftTrialPower

/-! One before-cutoff invoice for any nonempty subfamily of the actual three trial arms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftTrialCharge
open Function Filter Finset Lattice Laurent Wilson RG Labels Pert.Asymptotics
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalPublicTrialInput (vector)
open WilsonOriginalPublicTrialFigure (amount)
open WilsonOriginalPublicFigureIncome (height)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open WilsonOlderFreshSoftTrialSalary (base)
open WilsonOlderFreshSoftTrialPower (exposure)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){ι:Type}[Fintype ι][LinearOrder ι]

def bill (d:Fin 3→ℕ)(child:ι→Fin 3)(C:Fin 3→ℝ):ℝ:=∏i,4*base R d (child i)*C (child i)

def power (d:Fin 3→ℕ)(child:ι→Fin 3)(m:Fin 3→ℝ)(η:ℝ)(D₁ D₂:Fin 3→ℝ):ℝ:=
  ∑i,let a:=child i;exposure (d a) (height R (d a)) (m a) η (D₁ a) (D₂ a)

def wages (d j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))(before:∀a,j a≤K)
    (reg:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R d j target η M Y)
    (N per:ℕ)(child:ι→Fin 3):ℝ:=
  ∑b,‖WilsonOriginalPublicTrialFigure.weight R (d ∘ child) (regulatorRun R.family N per K)
    (fun i=>vector R d j K target η M Y before reg N per (child i)) b‖

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(d:Fin 3→ℕ):
    ∀ᶠ start:ℕ in atTop,∀(j:Fin 3→ℕ), (∀a,start≤j a) →
      (∀a,(R.family.path.levels.budget (j a)).supportExponent≤100) →
      ∀(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)(Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))
        (before:∀a,j a≤K)(reg:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R d j target η M Y)
        (N per:ℕ),K<N → 2≤R.family.path.levels.clock.hatBeta K → 0≤η → (∀a,0≤M a) →
      ∀(child:ι→Fin 3)(paid m C D₁ D₂:Fin 3→ℝ),
      let s:=Real.log (regulatorRun R.family N per K)⁻¹
      (∀a,0≤paid a) → (∀a,M a≤C a*Real.exp ((2*m a)*s)) →
      (∀a,Real.log (R.family.S.a K/R.family.S.a (j a))⁻¹≤D₁ a*s) →
      (∀a,paid a≤Real.exp ((d a:ℝ)*D₂ a*s)) →
      (∏i,paid (child i))*wages R d j K target η M Y before reg N per child≤
        bill R d child C*Real.exp (power R d child m η D₁ D₂*s):=by
  choose floor bound using fun a:Fin 3=>eventually_atTop.mp (WilsonOlderFreshSoftTrialSalary.wrapping R simple shop (d a))
  filter_upwards [eventually_ge_atTop (∑a,floor a)] with start onset
  intro j old support K target η M Y before reg N per live warm η0 M0 child paid m C D₁ D₂
  dsimp only
  intro p0 income span position
  have paper (a:Fin 3):1+wrapCost R (d a) (j a)≤WilsonOlderFreshSoftTrialSalary.wrap R (d a)*
      (R.family.path.levels.clock.hatBeta (j a))^2:=
    bound a (j a) (((single_le_sum (f:=floor) (fun _ _=>Nat.zero_le _) (mem_univ a)).trans onset).trans (old a)) (support a)
  have g0:=(WilsonOlderFreshSoftTrialPower.heat R simple N per K K le_rfl live.le).1
  have band:=(R.makes.wilson.represents N per K live.le).band.1
  change R.family.path.levels.clock.hatBeta K/2≤R.family.path.β N per K at band
  have g1:regulatorRun R.family N per K≤1:=by
    change (Real.sqrt (R.family.path.β N per K))⁻¹≤1
    exact inv_le_one_of_one_le₀ ((Real.one_le_sqrt).mpr (by linarith only [warm,band]))
  have wage:=WilsonOlderFreshSoftTrialSalary.purchased R d j K target η M Y before reg N per live child _ g0 g1 M0 paper
  apply (mul_le_mul_of_nonneg_left wage (prod_nonneg fun i _=>p0 (child i))).trans
  apply WilsonOlderFreshSoftTrialPower.total
  · intro i;unfold WilsonOlderFreshSoftTrialSalary.base WilsonOlderFreshSoftTrialSalary.wrap;positivity
  · intro i;exact (zero_lt_one.trans (R.family.path.levels.fits.delayed (j (child i)))).le
  · exact fun i=>p0 (child i)
  · exact fun i=>M0 (child i)
  · exact η0
  · exact fun i=>(WilsonOlderFreshSoftTrialPower.heat R simple N per _ K (before (child i)) live.le).2
  · exact fun i=>income (child i)
  · exact fun i=>span (child i)
  · exact fun i=>position (child i)

end YM.Integration.WilsonOlderFreshSoftTrialCharge
end
