import YM.Integration.WilsonPositionBarePointCoefficient
import YM.Integration.WilsonPositionBareDetectorGrowth

/-! Price the normalized and bare position tensors on the same cleared compact tuples of
the original auxiliary prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProtectedTuplePrice
open Filter Set Finset Function Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land PowerSeries Asymptotics
open WilsonPositionRawFiling WilsonPositionRawMesh
open scoped BigOperators Classical Topology
variable {G : Gauge} (Z : WilsonPrescription G) {g : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M T dial)
    {n d : ℕ} (v : Tags G d n) (q : ℕ) {r : ℝ} {K : Set (Points n)}
    (compact : IsCompact K) (sep : K ⊆ conf n) (hr : 0<r)
local notation "𝓛" => Notch.Pitch.frame r K
local notation "A" => Scale.Measure.adjust Z.scheme Z.criterion d

include H compact sep hr in
theorem forms :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ i : ℕ in atTop, ∀ s : Sample n, s.F = Z.run.step i →
      Notch.Entry r s → familiar s ∈ K → ∀ k ≤ q, ‖Speed.forms_t Z.scheme Z.criterion s d k v‖ ≤ C := by
  have hstep (k : ℕ) : Expense.Cap 𝓛 (fun s:Sample n=>Speed.forms_t Z.scheme Z.criterion s d k v) := by
    simp_rw [Speed.forms_t,Dframe.seen]
    apply IsBigO.sum
    intro a _
    let P := Notch.Pitch.phase 0 Z.scheme Z.criterion T M g H.details.born.Taylor H.details.born.still
      H.details.born.base r compact sep hr (pulseU a A v) (a none)
    exact Speed.Fast.higher (Notch.Pitch.stretches r K) P.quote P.sails
  choose c hc h using fun k : Fin (q+1) => (hstep k).bounds
  let C := ∑ k, c k
  have hC : 0 ≤ C := sum_nonneg fun k _=>(hc k).le
  have h' : ∀ᶠ s : Sample n in 𝓛, ∀ k ≤ q, ‖Speed.forms_t Z.scheme Z.criterion s d k v‖ ≤ C := by
    filter_upwards [eventually_all.mpr h] with s hs k hk
    exact (hs ⟨k,by omega⟩).trans (single_le_sum (f:=c) (fun j _=>(hc j).le) (mem_univ _))
  rw [Notch.Pitch.frame,eventually_inf_principal,eventually_comap] at h'
  refine ⟨C,hC,?_⟩
  filter_upwards [(goesFront (Expense.Stretched.runs Z.run)).eventually h'] with i hi s hm h1 h2
  exact hi s hm ⟨h1,h2⟩

def weight (m : Mesh) : ℝ := (q+1:ℕ)*(1+mass Z m q)

private theorem weight_one (m : Mesh) : 1 ≤ weight Z q m := by
  unfold weight
  have h : 0 ≤ mass Z m q := sum_nonneg fun _ _=>abs_nonneg _
  have hq : 1 ≤ ((q+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos q
  nlinarith

private theorem powers (m : Mesh) (e : ℕ) : ∀ k ≤ q,
    ‖coeff k (Rose.chosen Z.scheme Z.criterion m^e)‖ ≤ weight Z q m^e := by
  let D := Rose.chosen Z.scheme Z.criterion m
  let w := weight Z q m
  have hw : 1≤w := weight_one Z q m
  have hD (j : ℕ) (hj : j≤q) : ‖coeff j D‖ ≤ mass Z m q := by
    let u : Fin (q+1) := ⟨j,by omega⟩
    have real : (detector Z m q u : ℂ) = coeff j D := (key Z m).real.native _
    rw [←real,Complex.norm_real,Real.norm_eq_abs]
    exact single_le_sum (f:=fun k=>|detector Z m q k|) (fun _ _=>abs_nonneg _) (mem_univ _)
  induction e with
  | zero =>
    intro k _
    simp only [pow_zero,coeff_one]
    split_ifs <;> simp
  | succ e ih =>
    intro k hk
    change ‖coeff k (D^(e+1))‖ ≤ w^(e+1)
    rw [pow_succ,coeff_mul,pow_succ]
    calc
      _ ≤ ∑ j∈Finset.HasAntidiagonal.antidiagonal k, ‖coeff j.1 (D^e) * coeff j.2 D‖ := norm_sum_le .. 
      _ ≤ ∑ _j∈Finset.HasAntidiagonal.antidiagonal k, w^e * mass Z m q := by
        apply sum_le_sum
        intro j hj
        have he : j.1+j.2 = k := by simpa using hj
        rw [norm_mul]
        exact mul_le_mul (ih _ (by omega)) (hD _ (by omega)) (norm_nonneg _)
          (pow_nonneg (zero_le_one.trans hw) _)
      _ ≤ w^e*w := by
        rw [sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul]
        have hk' : ((k+1:ℕ):ℝ) ≤ ((q+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_le_succ hk)
        have hm : 0 ≤ mass Z m q := sum_nonneg fun _ _=>abs_nonneg _
        have h' : ((k+1:ℕ):ℝ)*mass Z m q ≤ w := mul_le_mul hk' (by linarith) hm (by positivity)
        calc _ = w^e * (((k+1:ℕ):ℝ)*mass Z m q) := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_left h' (pow_nonneg (zero_le_one.trans hw) _)

include H compact sep hr in
theorem actual :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i : ℕ in atTop,
      ∀ {B} (P : Handoff.Directory Z i B) (_cover : Handoff.Directory.budget G n d + q ≤ B),
      ∀ s : Sample n, s.F = Z.run.step i → Notch.Entry r s → familiar s ∈ K →
      ∀ u : ℝ, |u| ≤ 1 →
        ‖∑ k∈range (q+1), WilsonPositionOriginalEpochQuadrature.point P d v s.layout k*(u:ℂ)^k‖ ≤
          C*weight Z q (Z.run.step i)^q := by
  obtain ⟨c,hc,fees⟩ := forms Z H v q compact sep hr
  refine ⟨((q+1:ℕ):ℝ)^2*c,by positivity,?_⟩
  have use := (goesFront (Expense.Stretched.runs Z.run)).eventually (Rose.usable Z.scheme Z.criterion g)
  filter_upwards [fees,use] with i h use' B P cover s hs he hK u hu
  let m := Z.run.step i
  let w := weight Z q m
  let x := Reg.Point.story (Speed.forms_t Z.scheme Z.criterion s d) v
  let D := Rose.chosen Z.scheme Z.criterion m
  have hw := weight_one Z q m
  have z : constantCoeff D = 0 := Rose.zero_choice ..
  have ck (k : ℕ) (hk : k ≤ q) :
      ‖WilsonPositionOriginalEpochQuadrature.point P d v s.layout k‖ ≤ ((q+1:ℕ):ℝ) * (c * w^q) := by
    rw [WilsonPositionBarePointCoefficient.read P d v s hs use' k (by omega)]
    change ‖coeff k (PowerSeries.subst D x)‖ ≤ _
    rw [FPS.coeff_substituted x z k]
    calc
      _ ≤ ∑ j∈range (k+1), ‖coeff j x • coeff k (D^j)‖ := norm_sum_le ..
      _ ≤ ∑ _j∈range (k+1), c*w^q := by
        apply sum_le_sum
        intro j hj
        have hj' : j≤q := by have := mem_range.mp hj; omega
        have hx : ‖coeff j x‖≤c := by simpa only [x,Reg.Point.story,coeff_mk] using h s hs he hK j hj'
        rw [smul_eq_mul,norm_mul]
        exact mul_le_mul hx ((powers Z q m j k hk).trans (pow_le_pow_right₀ hw hj')) (norm_nonneg _) hc
      _ ≤ _ := by
        rw [sum_const,card_range,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hk) (mul_nonneg hc (pow_nonneg (zero_le_one.trans hw) _))
  calc
    _ ≤ ∑ k∈range (q+1), ‖WilsonPositionOriginalEpochQuadrature.point P d v s.layout k*(u:ℂ)^k‖ := norm_sum_le ..
    _ ≤ ∑ _k∈range (q+1), ((q+1:ℕ):ℝ)*(c*w^q) := by
      apply sum_le_sum
      intro k hk
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      simpa only [mul_one] using
        mul_le_mul (ck k (by have := mem_range.mp hk; omega)) (pow_le_one₀ (abs_nonneg u) hu)
          (pow_nonneg (abs_nonneg _) _) (by positivity : (0:ℝ) ≤ ((q+1:ℕ):ℝ) * (c*w^q))
    _ = _ := by rw [sum_const,card_range,nsmul_eq_mul]; change _ = ((q+1:ℕ):ℝ)^2*c*w^q;ring

end YM.Integration.WilsonPositionProtectedTuplePrice
