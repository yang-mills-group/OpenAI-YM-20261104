import YM.Integration.FVA1Physical.Wilson.OrbitExterior
import YM.Integration.FVA1Physical.Wilson.PurchasedReadout

/-! Orbit-coordinate disintegration of the normalized physical kernel. Only the
exterior orbit marginal is retained from the interacting measure. -/
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

def innerOrbit (A : Mosaic.Issue G) (J : Voice G) (x : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (B : Positions (Primary A.f G)→ℝ) (φ : Config G A.f→ℝ) : Config G A.f → ℝ :=
  let X:=boxX x b
  let Y:=boxY x b
  let V:=represent (tint G (Exterior.Body 1 A.c) z)
  let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) z
  let copy:=chambers A.F Y J V μ
  let area:=hotel A.F X Y J V μ (pillow x) (room x)
  orbitKernel A.F (board A.F X) area (interiorEnergy A.S V A.v copy A.pre.beta A.fClock B) φ

lemma innerOrbit_unit (A : Mosaic.Issue G) (J : Voice G) (x : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (B : Positions (Primary A.f G)→ℝ) (U : Config G A.f) :
    innerOrbit A J x z b B 1 U=1 := orbitKernel_unit ..

lemma innerOrbit_invariant (A : Mosaic.Issue G) (J : Voice G) (x : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (B : Positions (Primary A.f G)→ℝ) (φ : Config G A.f→ℝ)
    (t : IV A.F (board A.F (boxX x b)) G) (U : Config G A.f) :
    innerOrbit A J x z b B φ (twirl A.F (board A.F (boxX x b)) t U)=innerOrbit A J x z b B φ U :=
  orbitKernel_invariant ..

theorem purchased_orbit (J : Voice G) (cle : Clear G J) (simple : G.Simple)
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
      ∀ φ : Config G A.f→ℝ, GaugeLocal A.S (youth A.F (boxY v b)) φ → (∀ U,|φ U|≤1) →
        |expect A.S A.pre O (innerOrbit A J v z b B φ)-expect A.S A.pre O φ| ≤ 9*g^q := by
  obtain ⟨p,buy⟩ := purchased_chart_chance J cle simple H H' P K branches hD (-q)
  by_cases ok : 0 < p.gap ∧ 0 < p.a ∧ 0 < p.density
  swap
  · filter_upwards [buy] with x acquire
    intro A z b patch kernel season hb
    have h := (acquire A patch kernel season z b hb).1.buys
    exact False.elim (ok ⟨h.pos_m,h.pos_a,h.pos_C⟩)
  have rise := Work.E09.betaF_growth G P.L
  filter_upwards [buy,forest_scales G P hq hη,fees p P J cle,
    solders P K J H H' p cle ok.1 ok.2.1 ok.2.2,rise.eventually (bounded_hotel_radii p J cle hD),
    (Real.tendsto_log_atTop.comp rise).eventually_ge_atTop 1] with x acquire scales sizes tinting radius log
  intro A z b patch kernel season hb B bcont g v w O rows φ localφ φb
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
  have tact := paid.turn
  rw [Real.rpow_zero] at tact
  have cut := exterior_orbit_price W adm season.shine season.bends.1 pc.decent
    ((half_pos (zero_lt_one.trans v₁)).le.trans pc.beta) B bcont hg hw fit (Real.rpow_nonneg hg.le _)
    rows tact paid.sails φ localφ φb
  let d := motionCost G X w*(g^(q+η)/w)
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two hw.le))
    (div_nonneg (Real.rpow_nonneg hg.le _) hw.le)
  have twice := mul_nonneg zero_le_two hd
  have exponential := Real.abs_exp_sub_one_le (x:=2*d) (by rw [abs_of_nonneg twice]; linarith only [inc,half])
  rw [abs_of_nonneg twice] at exponential
  change |expect A.S A.pre O (innerOrbit A J v z b B φ)-expect A.S A.pre O φ| ≤
    v^(-q)+(Real.exp (2*d)-1)+4*v^(-q) at cut
  exact cut.trans (by linarith only [sup,inc,(le_abs_self _).trans exponential])

noncomputable def orbitThreshold (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) (branches : P.Branches K G)
    {D q η : ℝ} (hD : 0≤D) (hq : 0<q) (hη : 0<η) : ℝ :=
  (eventually_atTop.mp (purchased_orbit J cle simple H H' P K branches hD hq hη)).choose

end YM.Integration.FVA1Physical.Wilson
