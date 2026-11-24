import YM.Integration.WilsonThermometerCourseResidual

/-! The seven occupied and unoccupied coefficients on one measured three-source post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCourseMoments
open Finset Function MeasureTheory Lattice Wilson RG Source Marker FVA1 OPE.Therm
open Extraction Table Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open OriginalForcedAddresses MergeProof MergeProof.Accent MergeProof.East Extra.Trajectories ConnectedActivityE6
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerCourseIntake
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open WilsonThermometerCourseResidual
open scoped Classical BigOperators Topology

local notation "J" => Stock.census (Fin 3)
local notation "modes" => (Fintype.card ((J).Mode) : ℝ)

private theorem third (x : Poly J) :
    Poly.pass x = 1 + x + (2 : ℂ)⁻¹ • x^2 + (6 : ℂ)⁻¹ • x^3 := by
  norm_num [Poly.pass,Finset.sum_range_succ,Nat.factorial]

/-- The native price multiplies the three paid marker radii before estimating
the exponential. Only its single outgoing face toll is subsequently restored. -/
theorem seven (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) (p q : Poly J) {M : ℝ}
    (hp : Poly.price w p ≤ M) (hq : Poly.price w q ≤ M) :
    Poly.price w (Poly.pass p - Poly.pass q) ≤ (1+M)^2*Poly.price w (p-q) := by
  let δ := Poly.price w (p-q)
  have m0 := (Poly.nonnegative hw p).trans hp
  have d0 := Poly.nonnegative hw (p-q)
  have two : Poly.price w (p^2-q^2) ≤ 2*M*δ := by
    convert power_price p q w hw hp hq 1 using 1
    norm_num [δ]
  have three : Poly.price w (p^3-q^3) ≤ 3*M^2*δ := by
    convert power_price p q w hw hp hq 2 using 1
    norm_num [δ]
  have grouping : Poly.pass p - Poly.pass q =
      (p-q) + (2 : ℂ)⁻¹ • (p^2-q^2) + (6 : ℂ)⁻¹ • (p^3-q^3) := by
    rw [third p,third q,smul_sub,smul_sub]
    abel
  have halves : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  have sixths : ‖(6 : ℂ)⁻¹‖ = (6 : ℝ)⁻¹ := by norm_num
  rw [grouping]
  calc
    _ ≤ (δ + (2 : ℝ)⁻¹ * Poly.price w (p^2-q^2)) +
        (6 : ℝ)⁻¹ * Poly.price w (p^3-q^3) := by
      refine (Poly.addition hw ..).trans (add_le_add (Poly.addition hw ..) le_rfl |>.trans_eq ?_)
      simp only [Poly.adapted,halves,sixths,δ]
    _ ≤ (δ+(2 : ℝ)⁻¹*(2*M*δ))+(6 : ℝ)⁻¹*(3*M^2*δ) :=
      add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left two (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)) δ)
        (mul_le_mul_of_nonneg_left three (show 0 ≤ (6 : ℝ)⁻¹ by norm_num))
    _ = (1+M+M^2/2)*δ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg M]) d0

private theorem recovered (P Q : Poly J) (unit : P.part (J).quiet = 1)
    (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (s : (J).Mode)
    (loss : ℕ) {ε K g : ℝ} (ee : 0 ≤ ε) (pos : 0 < g)
    (radii : ∀ t : (J).Mode, g^loss ≤ Poly.toll w t)
    (enrolled : ∀ t : (J).Mode, Poly.toll w t*‖(logTo 3 P-Q).part t‖ ≤ ε*g^(loss+4))
    (price : g^2*(1+(Poly.price w Q+modes*ε*g^(loss+4)))^2 ≤ K) :
    ‖P.part s-(Poly.pass Q).part s‖ ≤ modes*K*ε*g^2 := by
  let L := logTo 3 P
  let δ := modes*ε*g^(loss+4)
  let M := Poly.price w Q + δ
  have delta0 : 0 ≤ δ := by dsimp only [δ]; positivity
  have compare : Poly.price w (L-Q) ≤ δ := calc
    _ ≤ ∑ _s : (J).Mode,ε*g^(loss+4) := Finset.sum_le_sum (fun t _ => enrolled t)
    _ = _ := by simp [δ,mul_assoc]
  have hold : Poly.price w L ≤ M := calc
    _ = Poly.price w ((L-Q) + Q) := by rw [sub_add_cancel]
    _ ≤ Poly.price w (L-Q) + Poly.price w Q := Poly.addition hw .. 
    _ ≤ M := (add_le_add_left compare _).trans_eq (add_comm ..)
  have room (t : (J).Mode) : t.val.card ≤ 3 := by simpa using t.val.card_le_univ
  have kept : Poly.pass L = P :=
    (congrArg Poly.pass (log_to _ unit 3 room).symm).trans (pass_connected unit)
  have coefficient := (Poly.member hw s (P-Poly.pass Q)).trans
    ((show Poly.price w (P-Poly.pass Q) ≤ (1+M)^2*Poly.price w (L-Q) from
        (seven w hw L Q hold (le_add_of_nonneg_right delta0))
          |> fun h => (congrArg (fun v => Poly.price w (v-Poly.pass Q)) kept.symm).le.trans h).trans
      (mul_le_mul_of_nonneg_left compare (sq_nonneg _)))
  have bound : g^loss * ‖P.part s-(Poly.pass Q).part s‖ ≤
      g^loss*(modes*K*ε*g^2) := calc
    _ ≤ Poly.toll w s * ‖(P-(Poly.pass Q)).part s‖ :=
      mul_le_mul_of_nonneg_right (radii s) (norm_nonneg _)
    _ ≤ (1+M)^2*δ := coefficient
    _ = (g^2*(1+M)^2)*(g^loss*modes*ε*g^2) := by dsimp only [δ];rw [pow_add];ring
    _ ≤ K*(g^loss*modes*ε*g^2) :=
      mul_le_mul_of_nonneg_right (price) (by positivity)
    _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (pow_pos pos loss)).mp bound

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
  {N per i m : ℕ} (live : i < N) (floor : m ≤ i) (o : Positions (Fin 3) (R.family.side N per))
local notation "C" => R.family
local notation "W₀" => Config G (R.family.side i per)
local notation "gs" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "gm" => Coat.gStep (R.family.path.rep N per m).beta
local notation "T" => table R A simple live.le o
local notation "L" W => logTo 3 ((T) W)

include floor in
/-- From the paid finite table on a real subdomain to its raw physical moments.
All unadmitted group fields retain the complete deposited Wilson table. -/
theorem original (ref : ∀ h : Fin 3, R.family.ref (grade h) ≤ N)
    (E : Set W₀) (F : W₀ → Poly J) (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (loss : ℕ) {ε K : ℝ} (ee : 0 ≤ ε) (kk : 0 ≤ K)
    (radii : ∀ s : (J).Mode, (gs)^loss ≤ Poly.toll w s)
    (enrolled : ∀ W ∈ E, ∀ s : (J).Mode,
      Poly.toll w s*‖((L W)-F W).part s‖ ≤ ε*(gs)^(loss+4))
    (price : ∀ W ∈ E, (gs)^2*(1+(Poly.price w (F W)+modes*ε*(gs)^(loss+4)))^2 ≤ K)
    {u : ℕ} (old : u ≤ i) :
    let Q := fun W => if W ∈ E then Poly.pass (F W) else (T) W
    ∀ s : (J).Mode,
      let err := fun W => ((gm)^7 : ℝ) • (((T) W).part s - (Q W).part s)
      (∀ W, ‖actualTransport C (N:=N) err old W‖ ≤ 4*modes*K*ε*(gm)^9) ∧
      ‖∫ W,actualTransport C (N:=N) err old W ∂scene (C).path N per u‖ ≤ 4*modes*K*ε*(gm)^9 := by
  intro Q s err
  have pos : 0 < gs := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have report : 0 ≤ gm := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have band : (gs) ≤ 2*(gm) :=
    WilsonLocalCompactRichPortUnits.compared R simple (floor.trans (Nat.le_succ i)) live per
  have paid (W : W₀) : ‖err W‖ ≤ 4*modes*K*ε*(gm)^9 := by
    by_cases h : W ∈ E
    · have unit : ((T) W).part (J).quiet = 1 := by
        rw [observed R A simple live.le o ref W]
        simp only [show (J).quiet.val = (∅ : Finset (Fin 3)) from rfl,Finset.prod_empty]
        exact actualTransport_const C R.makes le_rfl 1 live.le W
      have facePrice := recovered ((T) W) (F W) unit w hw s loss ee pos radii (enrolled W h) (price W h)
      dsimp only [err,Q]
      rw [if_pos h,norm_smul,Real.norm_of_nonneg (pow_nonneg report _)]
      calc
        _ ≤ (gm)^7*(modes*K*ε*(gs)^2) := mul_le_mul_of_nonneg_left facePrice (pow_nonneg report _)
        _ ≤ (gm)^7*(modes*K*ε*(2*(gm))^2) := by gcongr
        _ = _ := by ring
    · simp only [err,Q,if_neg h,sub_self,smul_zero,norm_zero]; positivity
  have every := actualTransport_norm_le C R.makes live.le paid old
  letI : IsProbabilityMeasure (scene (C).path N per u) := probability R.makes.wilson (old.trans live.le)
  refine ⟨every,?_⟩
  simpa using norm_integral_le_of_norm_le_const (μ:=scene (C).path N per u) (ae_of_all _ every)

end YM.Integration.WilsonThermometerCourseMoments
end
