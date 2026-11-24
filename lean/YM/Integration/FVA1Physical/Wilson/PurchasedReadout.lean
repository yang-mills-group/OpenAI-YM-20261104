import YM.Integration.FVA1Physical.Wilson.HaarReadout
import YM.Integration.FVA1Physical.Wilson.ForestCash
import YM.Integration.FVA1Physical.Wilson.ForestScales

/-! The entire normalized inherited local reading against the independent polynomial
in the copied coordinates. Native exterior and failed sectors are integrated at
their actual mass. No pointwise bound on the physical forest density remains. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum Pressure
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology
variable {G : Gauge}

/-- The physical free-link resampler, with only the independently prescribed
polynomial in the energy increment, using the unrestricted interacting vacuum. -/
def forestTicket (A : Mosaic.Issue G) (J : Voice G) (x : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (B : Positions (Primary A.f G)→ℝ) (φ : Config G A.f→ℝ) : ℝ :=
  let X:= boxX x b
  let Y:= boxY x b
  let V:= represent (tint G (Exterior.Body 1 A.c) z)
  let μ:= vest (priced A.F A.v A.pre.clip A.pre.path) z
  let copy:= chambers A.F Y J V μ
  let area:=hotel A.F X Y J V μ (pillow x) (room x)
  let r:=woolModel A.F X J A.pre Y A.v V μ (pillow x) (room x)
  let τ:=fun U=>B (chartLog A.fClock (copy U))
  let Z:=A.S.push A.pre.beta A.pre.eval V
  ∫ θ : IV A.F (board A.F X) G,A.S.push A.pre.beta (fun U=>Rota.ghat r θ φ area U *
     (A.pre.eval (twirl A.F (board A.F X) θ U)*Real.exp (τ U-τ (twirl A.F (board A.F X) θ U)))) V/Z
    ∂fence A.F (board A.F X) G

theorem purchased_haar_readout (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) (branches : P.Branches K G)
    {D q η : ℝ} (hD : 0≤D) (hq : 0<q) (hη : 0<η) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D → ∀ B : Positions (Primary A.f G)→ℝ, Continuous B →
      let g:=A.fClock
      let v:=tip G P.L x
      let w:=Mosaic.vol v
      let O:=represent (tint G (Exterior.Body 1 A.c) z)
      (∀ a u : Positions (Primary A.f G), (∀ t∈Set.Icc (0:ℝ) 1,a+t • u∈Metric.closedBall 0 w) →
       |(Real.log (A.pre.eval (palace (g • (a+u)))) - B (a+u)) -
         (Real.log (A.pre.eval (palace (g • a)))-B a)|≤(∑ j,|u j|)*(g^(q+η)/w)) →
      ∀ φ : Config G A.f→ℝ, GaugeLocal A.S (youth A.F (boxY v b)) φ → 0≤φ → (∀ U,φ U≤1) →
        |forestTicket A J v z b B φ-expect A.S A.pre O φ| ≤ 10*g^q := by
  obtain ⟨p,buy⟩ := purchased_chart_chance J cle simple H H' P K branches hD (-q)
  by_cases ok : 0 < p.gap ∧ 0 < p.a ∧ 0 < p.density
  swap
  · filter_upwards [buy] with x acquire
    intro A z b patch kernel season hb
    have h := (acquire A patch kernel season z b hb).1.buys
    exact False.elim (ok ⟨h.pos_m,h.pos_a,h.pos_C⟩)
  have rise := Work.E09.betaF_growth G P.L
  filter_upwards [buy,forest_cash J cle H H' P K p (-q),forest_scales G P hq hη,fees p P J cle,
    solders P K J H H' p cle ok.1 ok.2.1 ok.2.2,rise.eventually (bounded_hotel_radii p J cle hD),
    (Real.tendsto_log_atTop.comp rise).eventually_ge_atTop 1] with x acquire cash scales sizes tinting radius log
  intro A z b patch kernel season hb B bcont g v w O rows φ localφ φ₀ φb
  obtain ⟨give,paid,_,_⟩ := acquire A patch kernel season z b hb
  have pc := season.case_
  rw [patch] at pc
  obtain ⟨v₁,_,_,_,_,_,_,_,_,_,_,_,rad,garden⟩ := sizes
  have band := Mosaic.ever (zero_lt_one.trans v₁) pc.beta pc.upper
  have shield := (tinting A.pre A.post pc season.hull).holm
  let X := boxX v b
  let Y := boxY v b
  let μ := vest (priced A.F A.v A.pre.clip A.pre.path) z
  let W : ForestCell A.S A.pre A.post :=
    ⟨A.F,X,Y,J,p,z,μ,pillow v,room v,base J v,rot p v,voyageB v,radiusB v,v^(-(1:ℝ)),3,A.v,
      cle,paid.first,shield,give,rad,garden⟩
  have fit : W.Fits g w := radius g band ‖z‖ ‖μ‖ (norm_nonneg _) hb
    (fun hz=>terror A.F A.v p z give le_rfl hz)
  have hw : 0<w := div_pos (sq_pos_of_pos (zero_lt_one.trans_le log)) (by norm_num)
  obtain ⟨hg,sup,half,inc⟩ := scales A.f b A.pre.beta w hw pc.beta pc.upper
  change motionCost G X w*(g^(q+η)/w) ≤ g^q at inc
  change v^(-q)≤g^q at sup
  change g^q≤1/2 at half
  have power : 0 ≤ v^(-q) := Real.rpow_nonneg (zero_lt_one.trans v₁).le _
  have mass : 0<A.S.push A.pre.beta A.pre.eval O := by
    rw [←season.taskEval]; unfold Rep.eval
    rw [Activities.gas_one _ _ (voids paid.first.folds shield),mul_one]
    exact Real.exp_pos _
  have adm : Admitted O A.pre A.S H'.width H'.paths (ability v) (lbt v) 1 :=
    ⟨pc.lawful,fun Q=>(season.shine Q).le,mass,A.S.isKernel season.bends.1 _⟩
  obtain ⟨_,fee,forced⟩ := cash A z b patch kernel season give paid
  have small : motionCost G X w*(g^(q+η)/w)+v^(-q)≤1 := by linarith only [inc,sup,half]
  have tact := paid.turn
  rw [Real.rpow_zero] at tact
  have primal := forest_haar_price W adm season.shine season.bends.1 pc.decent ((half_pos (zero_lt_one.trans v₁)).le.trans pc.beta)
    season.primal season.storm shield (Real.exp_pos _).le B bcont hg hw fit (Real.rpow_nonneg hg.le _) power fee small rows tact φ localφ φ₀ φb
  let ζ := Real.exp (Posture.wSize G A.pre.p H'.width H'.paths (ability v) (lbt v) A.pre.beta (voyageB v) Y.card X.card p (rot p v) (room v)) / Posture.moss G (v^(-(1:ℝ))) (board A.F X).card
  let F := courage G P.L x*(A.pre.p.mass (youth A.F Y) (ζ*2)*Real.exp ((youth A.F Y).card* (1:ℝ)))
  have Fcap : F≤g^q := forced.trans sup
  have e₀ : 0≤ motionCost G X w*(g^(q+η)/w)+v^(-q) :=
    add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two hw.le)) (div_nonneg (Real.rpow_nonneg hg.le _) hw.le)) power
  have work : 1+v^(-q)+F≤2 := by linarith only [sup,half,Fcap]
  have mix := mul_le_mul_of_nonneg_left work (mul_nonneg zero_le_two e₀)
  dsimp only at primal
  have normal : (ζ * 1 * 2) = ζ * 2 := by rw [mul_one]
  change |forestTicket A J v z b B φ-expect A.S A.pre O φ| ≤
    courage G P.L x*(A.pre.p.mass (youth A.F Y) (ζ*1*2)*Real.exp ((youth A.F Y).card* (1:ℝ))) +
    2*(motionCost G X w*(g^(q+η)/w)+v^(-q))*(1+v^(-q)+courage G P.L x*(A.pre.p.mass (youth A.F Y) (ζ*1*2)*Real.exp ((youth A.F Y).card* (1:ℝ))))+v^(-q) at primal
  rw [normal] at primal
  change |forestTicket A J v z b B φ-expect A.S A.pre O φ| ≤ F+2*(motionCost G X w*(g^(q+η)/w)+v^(-q))*(1+v^(-q)+F)+v^(-q) at primal
  exact primal.trans (by linarith only [Fcap,inc,sup,mix])

/-- A numerical construction-stage threshold. It can be fixed before a torus,
initial UV scale or physical source realization is specified. -/
noncomputable def forestThreshold (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) (branches : P.Branches K G)
    {D q η : ℝ} (hD : 0≤D) (hq : 0<q) (hη : 0<η) : ℝ :=
  (eventually_atTop.mp (purchased_haar_readout J cle simple H H' P K branches hD hq hη)).choose

end YM.Integration.FVA1Physical.Wilson
