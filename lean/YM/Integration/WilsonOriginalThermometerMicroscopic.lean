import YM.Integration.WilsonOriginalAdjacentMicroscopicPrice
import YM.Integration.WilsonOriginalThermometerRealPalette
import YM.RG01.Slack

/-! At the first nonbare block the entire microscopic field of each inverse-fitted
thermometer leg has a polynomial cap.  The constants are fixed before the
reporting date, chosen station, period, placement and field. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalThermometerMicroscopic
open Filter Finset Lattice Wilson RG Source Labels FVA1 WilsonLimitConstruction PhysicalNext.Repeat
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
local notation "C" => R.family
local notation "V" => R.family.path.levels
local notation "B" n:max => R.family.path.levels.clock.hatBeta n

def mass : ℝ := ∑ j:Fin 3, WilsonPositionThermometerStationNorm.cost C (levels j) *
  (1+‖source C univ j‖)

def close (A : Group C 6) : Prop := ∀ j:Fin 3, ‖vector A univ j-source C univ j‖ ≤ 1

theorem projected {S : Table (C).book} {Y : Ultrafilter (ℕ × ℕ)} {m : ℕ} {r : ℝ}
    {A : Group C 6} {P : PhysMS.tower S}
    (h : projects (f:=f) (Y:=Y) H (fun z:Finset (Fin 3) × Fin 3=>grade z.2)
      (fun z=>source C z.1 z.2) A P m r) : A.station.checked f H A.horizon ∧ close R A := by
  refine ⟨h.2.1,fun j=>?_⟩
  have bound:=h.2.2.2.2.2 (univ,j)
  exact bound.trans (inv_le_one_of_one_le₀ (by change 1 ≤ (m:ℝ)+1; linarith [Nat.cast_nonneg (α:=ℝ) m]))

private theorem salary_le (A : Group C 6) (h : close R A) : salary R A ≤ mass R := by
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (by unfold WilsonPositionThermometerStationNorm.cost; positivity)
  calc
    ‖vector A univ j‖ = ‖(vector A univ j-source C univ j)+source C univ j‖ := by rw [sub_add_cancel]
    _ ≤ ‖vector A univ j-source C univ j‖ + ‖source C univ j‖ := norm_add_le _ _
    _ ≤ 1+‖source C univ j‖ := add_le_add (h j) (le_refl _)

theorem leg (simple : G.Simple) {δ : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} (fund : FundedOriginalProperties.{u} simple δ W)
    (slow : WilsonWindowReportingPace.Slow R.kit) :
    ∃ c:ℝ, 1≤c ∧ ∃ e:ℕ, ∀ᶠ i:ℕ in atTop, ∀ (A:Group C 6), A.station.k=i+1 →
      A.station.checked f H A.horizon → close R A →
      ∀ (p:ℕ) (j:Fin 3) (o:Site ((C).side (i+2) p)) (U:Config G ((C).side (i+2) p)),
        ‖(C).O (i+2) p (A.station.wheel.atCut (i+2,p) (index A (grade j)) (vector A univ j)) o U‖ ≤
        c*(B i)^e := by
  choose c one paid using fun j:Fin 3=> WilsonOriginalAdjacentMicroscopicPrice.entry R (levels j) simple fund slow
  let sumC:=∑ j,c j
  let d:=fun j:Fin 3=> WilsonOriginalAdjacentMicroscopicPrice.height R (levels j)+levels j+1
  let e:=∑ j,d j
  let M:=max 1 (mass R)
  have c1: 1 ≤ sumC:= (one 0).trans (single_le_sum (f:=c) (fun j _=>(zero_le_one.trans (one j))) (mem_univ 0))
  have up:1≤(4:ℝ)^e:=one_le_pow₀ (by norm_num) 
  have m1:1≤M:=le_max_left _ _
  refine ⟨(sumC*4^e)*(2*M),?_,e+1,?_⟩
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le c1 up) (one_le_mul_of_one_le_of_one_le (by norm_num) m1)
  obtain ⟨n,cal⟩:=eventually_atTop.mp (WilsonOriginalThermometerPalette.station R (f:=f) (H:=H) simple 1 zero_lt_one)
  obtain ⟨s,adj⟩:=eventually_atTop.mp (RG01.Physical.nextHat simple V)
  filter_upwards [eventually_ge_atTop n,eventually_ge_atTop s,(eventually_all.mpr
    (fun j:Fin 3=>eventually_ge_atTop ((C).ref (levels j))))] with i hn hs refs A date checked near p j o U
  let v:=A.station.wheel.atCut (i+2,p) (index A (grade j)) (vector A univ j)
  have cash:((C).labels.level (levels j)).coeffSize (coordinates R A (i+1) (i+2) p j) ≤ B (i+1)*M:=
    (by simpa only [Real.rpow_one] using cal (i+1) (by omega) A date checked (i+2) p (by omega) j :
      ((C).labels.level (levels j)).coeffSize (coordinates R A (i+1) (i+2) p j) ≤ B (i+1)*salary R A).trans
      (mul_le_mul_of_nonneg_left ((salary_le R A near).trans (le_max_right _ _))
        (zero_le_one.trans ((V).fits.delayed (i+1)).le))
  have next:=adj i hs
  have next2:=adj (i+1) (by omega)
  have both:B (i+2) ≤ 4*(B i):=by linarith
  have b1:=((V).fits.delayed i).le
  have large: 1 ≤ 4*(B i):=by linarith
  have root: (B (i+2))^(d j) ≤ (4*(B i))^e:= (pow_le_pow_left₀
      (zero_le_one.trans ((V).fits.delayed (i+2)).le) both _).trans
    (pow_le_pow_right₀ large (single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (mem_univ j)))
  have coeff: c j ≤ sumC:=single_le_sum (f:=c) (fun a _=>zero_le_one.trans (one a)) (mem_univ j)
  calc
    ‖(C).O (i+2) p v o U‖ ≤ c j * (B (i+2))^(d j) * ((C).labels.level (levels j)).coeffSize
      (coordinates R A (i+1) (i+2) p j) := paid j (i+1) ((refs j).trans (Nat.le_succ _)) p v o U
    _ ≤ (sumC*(4*(B i))^e)*(2*(B i)*M) := mul_le_mul
      (mul_le_mul coeff root (pow_nonneg (zero_le_one.trans ((V).fits.delayed (i+2)).le) _) (zero_le_one.trans c1)) (cash.trans
        (mul_le_mul_of_nonneg_right next (zero_le_one.trans m1))) (sum_nonneg fun _ _=>norm_nonneg _)
      (mul_nonneg (zero_le_one.trans c1) (pow_nonneg (zero_le_one.trans large) _))
    _ = (sumC*4^e)*(2*M)*(B i)^(e+1) := by rw [mul_pow,pow_succ];ring

theorem faces (simple : G.Simple) {δ : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} (fund : FundedOriginalProperties.{u} simple δ W)
    (slow : WilsonWindowReportingPace.Slow R.kit) :
    ∃ c:ℝ, 1≤c ∧ ∃ e:ℕ, ∀ᶠ i:ℕ in atTop, ∀ (A:Group C 6), A.station.k=i+1 →
      A.station.checked f H A.horizon → close R A →
      ∀ (p:ℕ) (s:Finset (Fin 3)) (o:Fin 3 → Site ((C).side (i+2) p)) (U:Config G ((C).side (i+2) p)),
      ‖∏ j∈s,(C).O (i+2) p (A.station.wheel.atCut (i+2,p) (index A (grade j)) (vector A univ j)) (o j) U‖^2 ≤
        c*(B i)^e := by
  obtain ⟨c,hc,e,all⟩:=leg R (f:=f) (H:=H) simple fund slow
  refine ⟨c^6,one_le_pow₀ hc,6*e,?_⟩
  filter_upwards [all] with i pay A date checked near p s o U
  have legPay:=pay A date checked near p
  let K:=c*(B i)^e
  have kp : 1≤K := one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ ((V).fits.delayed i).le)
  have size:s.card≤3:=by simpa using card_le_univ s
  have prod : ‖∏ j∈s,(C).O (i+2) p (A.station.wheel.atCut (i+2,p) (index A (grade j)) (vector A univ j)) (o j) U‖ ≤ K^3:=by
    rw [norm_prod]
    exact (prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>legPay j (o j) U)).trans
      (by simp only [prod_const];exact pow_le_pow_right₀ kp size)
  calc
    _ ≤ (K^3)^2 := pow_le_pow_left₀ (norm_nonneg _) prod _
    _ = c^6*(B i)^(6*e) := by dsimp only [K];rw [mul_pow,mul_pow,←pow_mul,←pow_mul,←pow_mul];ring_nf

end YM.Integration.WilsonOriginalThermometerMicroscopic
