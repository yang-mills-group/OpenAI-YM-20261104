import YM.Integration.WilsonRegisteredPlaquetteReading
import YM.RG05Readout.Pulse.Openly
import YM.Next.STATIONARY.FrameEst.Center

/-! The local thermal exception on the actual compact reporting stencil.
Both its polynomial spatial census and the signed source prices are consumed
before taking the cutoff and volume limits. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonReportingPlaquetteWindows
open Function Filter Finset MeasureTheory Lattice Wilson RG OPE.Therm RGComparison.Core16.Spool
open WilsonRegisteredWindowRestriction
open scoped Classical Topology BigOperators
variable {G : Gauge} {V A : Type} [Fintype V] [DecidableEq V] [Fintype A]

abbrev placements (C : Family G) (k per t : ℕ) := ↥(RG05Readout.Pulse.area (C:=C) (b:=k) (p:=per) (V:=V) t)

private theorem census (C : Family G) (k per t s : ℕ) {x : ℝ} (one : 1 ≤ x)
    (width : (t:ℝ) ≤ x^s) :
    (Fintype.card (placements (V:=V) C k per t):ℝ) ≤
      (3:ℝ)^(4*Fintype.card V)*x^(s*(4*Fintype.card V)) := by
  have finite := RG05Readout.Pulse.area_cost (C:=C) (p:=per) (b:=k) (V:=V) t
  have box : (Lattice.box t).card = (2*t+1)^4 := by
    simpa only [Fintype.card_coe] using Stationary.Audience.portrait_card t
  rw [box,←pow_mul] at finite
  have count : (Fintype.card (placements (V:=V) C k per t):ℝ) ≤
      (2*(t:ℝ)+1)^(4*Fintype.card V) := by
    simpa only [placements,Fintype.card_coe,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat,Nat.cast_one] using (Nat.cast_le (α:=ℝ)).mpr finite
  have span : 2*(t:ℝ)+1 ≤ 3*x^s := by linarith only [width,(show (1:ℝ) ≤ x^s from one_le_pow₀ one)]
  calc
    _ ≤ _ := count
    _ ≤ (3*x^s)^(4*Fintype.card V) := pow_le_pow_left₀ (by positivity) span _
    _ = _ := by rw [mul_pow,←pow_mul]

/-- Every later action regulator is admitted. The stencil may be born at
any j between the reporting date and that regulator. The weights can depend
on all dates, the period and the actual marked positions. -/
theorem original (C : Family G) (law : C.Makes) (stoves : Poetry C.path.levels) (simple : G.Simple)
    (J : A → V → Lamp G) (d s e q : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N per j, j ≤ N → ∀ low : k ≤ j, ∀ t : ℕ,
      (t:ℝ) ≤ C.path.levels.clock.hatBeta k^s →
      ∀ (w : placements (V:=V) C k per t × A → ℂ)
        (o : placements (V:=V) C k per t × A → V → Site (C.side j per))
        (cells : placements (V:=V) C k per t × A → V → Finset (Face (Per (C.side k per)))),
      (∀ a, ‖w a‖ ≤ C.path.levels.clock.hatBeta k^e) →
      (∀ a i, ((cells a i).card:ℝ) ≤ C.path.levels.clock.hatBeta k^d) →
      ∫ U, ‖∑ a, (⋃ i, (House.chilly (cells a i) (cool C.path.levels k))ᶜ).indicator
        (fun Z => w a * actualTransport C (N:=N) (tally (J a.2) (o a)) low Z) U‖
        ∂scene C.path N per k ≤ ε * Pert.Asymptotics.regulatorRun C N per k^q := by
  let v := Fintype.card V
  let B := ∑ a, wordBound (J a)
  have nb (a : A) : 0 ≤ wordBound (J a) := mul_nonneg (by norm_num) (encouraging (J a)).choose_spec.1
  have bp : 0 ≤ B := sum_nonneg (fun a _ => nb a)
  let K := (v:ℝ)*(3:ℝ)^(4*v)*B
  have kp : 0 ≤ K := by dsimp [K]; positivity
  have budget : 0 < ε/(K+1) := div_pos ep (by linarith only [kp])
  filter_upwards [rare stoves simple law.wilson,
    WilsonRegisteredPlaquetteReading.currency C law simple (d+(e+s*(4*v))) q budget] with k alarm funded
  intro N per j top low t width w o cells wb size
  let x := C.path.levels.clock.hatBeta k
  have one : 1 ≤ x := (C.path.levels.fits.delayed k).le
  have zero : 0 ≤ x := zero_le_one.trans one
  let z := vanishP C.path.levels k
  have rent : 0 ≤ z := (Real.exp_pos _).le
  let placements' := placements (V:=V) C k per t
  have count := census (V:=V) C k per t s one width
  have mass : (∑ a, ‖w a‖*wordBound (J a.2)) ≤
      ((3:ℝ)^(4*v)*x^(s*(4*v)))*(x^e*B) := by
    calc
      _ ≤ ∑ a : placements' × A, x^e*wordBound (J a.2) :=
        sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (wb a) (nb a.2))
      _ = (Fintype.card placements':ℝ)*(x^e*B) := by
        rw [Fintype.sum_prod_type]; simp only [←Finset.mul_sum,sum_const,card_univ,nsmul_eq_mul]; dsimp only [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right count (mul_nonneg (pow_nonneg zero _) bp)
  have live := low.trans top
  letI : IsProbabilityMeasure (scene C.path N per k) := probability law.wilson live
  have region (a : placements' × A) (i : V) :
      (scene C.path N per k).real ((House.chilly (cells a i) (cool C.path.levels k))ᶜ) ≤ x^d*z :=
    (House.cool_miss z (alarm N live per) (cells a i)).trans
      (mul_le_mul_of_nonneg_right (size a i) rent)
  have estimate := bank C law top low (fun a : placements' × A => J a.2) o w
    (fun a i => (House.chilly (cells a i) (cool C.path.levels k))ᶜ)
    (fun a i => (House.bath (G:=G) _).compl) (x^d*z) region
  have purchase := funded N per live
  let g := Pert.Asymptotics.regulatorRun C N per k
  have gp : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc
    _ ≤ _ := estimate
    _ ≤ ((v:ℝ)*(x^d*z))*(((3:ℝ)^(4*v)*x^(s*(4*v)))*(x^e*B)) :=
      mul_le_mul_of_nonneg_left mass (by positivity)
    _ = K*(x^(d+(e+s*(4*v)))*z) := by dsimp only [K];rw [pow_add,pow_add];ring
    _ ≤ K*((ε/(K+1))*g^q) := mul_le_mul_of_nonneg_left purchase kp
    _ ≤ ε*g^q := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg gp _)
      rw [←mul_div_assoc]
      exact (div_le_iff₀ (by linarith only [kp] : 0<K+1)).mpr (by nlinarith only [ep])

end YM.Integration.WilsonReportingPlaquetteWindows
