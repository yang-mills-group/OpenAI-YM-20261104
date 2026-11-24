import YM.Integration.WilsonGeometricSignedOrder
import YM.Integration.WilsonReceivedOrdinaryFaces

/-! The complete signed ordinary discrepancy on every actual empty-flag field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGeometricSignedClear
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open Push.Local Comparison.RG02.Cumulants WilsonGeometricSignedCapture WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {X ι ν : Type} {o : Fin 3 → Site n} {P : Rep G n}
local notation "J" => Stock.census (Fin 3)

theorem priced (L : Lamps X ι G P.p o J) (B : Lamps X ν G P.p o J) (H : Hard X P.p P.activities.forced P.activities.K o J)
    (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) {C e : ℝ} (ep : 0 ≤ e) (low : e ≤ 1) (cpos : 0 ≤ C)
    (model : L.Paid w P.p.B (P.p.supportExponent+2) C) (debt : B.Paid w P.p.B (P.p.supportExponent+2) e)
    (x : X) (c : (J).Mode → ℂ) (U : Config G n) (clear : flags P.p.threshold U = ∅) :
    let A : Gallery X (ι⊕ν) o P J := ⟨L.join B,H⟩
    let t : ℂ := (P.eval U:ℂ)
    ‖t⁻¹ * (take c (A.density x U) - t*take c (Poly.pass (bare L x U)))‖ ≤
      weightBill c w * (3*(Fintype.card (parts (J)).Mode:ℝ)*e*(C+2)^3) := by
  intro A t
  have width : 0 ≤ P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
  have l := model.sums width hw x U
  have b := debt.sums width hw x U
  have exp : P.eval U = Real.exp (P.exponent U) := by
    rw [Rep.eval,P.activities.gas_one (p:=P.p) clear,mul_one]
  have live : t ≠ 0 := Complex.ofReal_ne_zero.mpr (exp ▸ Real.exp_ne_zero _)
  have full : t⁻¹ • A.density x U = Poly.pass ((L.join B).log x U) := by
    rw [Gallery.density,WilsonFirstReceivedGalleryRegular.clear A x U clear,mul_one,←exp,
      smul_smul,inv_mul_cancel₀ live,one_smul]
  have raw : bare L x U = L.log x U := by
    apply tsum_congr
    intro a
    exact congrArg (Poly.send (L.mode a)) (sub_eq_zero.mp (healthy L x a U (by simp [Healthy,clear]))).symm
  let d (s : (J).Mode) := t⁻¹*((A.density x U).part s-t*(Poly.pass (bare L x U)).part s)
  have eq (s : (J).Mode) : d s = (Poly.pass ((L.join B).log x U)).part s-(Poly.pass (L.log x U)).part s := by
    have val:=congrArg (fun a:Poly J=>a.part s) full
    dsimp only [d]
    rw [mul_sub,←mul_assoc,inv_mul_cancel₀ live,one_mul,←Poly.part_smul,val,raw]
  have field : t⁻¹*(take c (A.density x U) - t*take c (Poly.pass (bare L x U))) = ∑ s, c s * d s := by
    rw [take,take,mul_sum,←sum_sub_distrib,mul_sum]
    exact sum_congr rfl fun s _ => by dsimp only [d]; ring
  let M := C+1
  have one : 1 ≤ M+e := by dsimp only [M]; linarith
  have old (p : Hot J) : Poly.toll w p.val * ‖((L.join B).log x U).part p.val-(L.log x U).part p.val‖ ≤ e := by
    rw [Lamps.joinLog x U l b]
    change Poly.toll w p.val * ‖(L.log x U).part p.val + (B.log x U).part p.val - (L.log x U).part p.val‖ ≤ e
    rw [add_sub_cancel_left]
    obtain ⟨v,hv⟩ := p.property
    exact WilsonFirstReceivedGalleryRegular.occupied B debt width hw x U p.val v hv
  have actual (p : Hot J) : Poly.toll w p.val*‖(L.log x U).part p.val‖ ≤ M := by
    obtain ⟨v,hv⟩ := p.property
    exact (WilsonFirstReceivedGalleryRegular.occupied L model width hw x U p.val v hv).trans (by dsimp only [M]; linarith)
  let K := 3*(Fintype.card (parts (J)).Mode:ℝ)*e*(C+2)^3
  have per (s : (J).Mode) : Poly.toll w s*‖d s‖ ≤ K := by
    rw [eq]
    have gg := WilsonReceivedOrdinaryFaces.ordinary ((L.join B).log x U) (L.log x U) w hw
      (by
        rw [Lamps.joinLog x U l b]
        change (L.log x U).part (J).quiet + (B.log x U).part (J).quiet = 0
        rw [L.quiet_of_hasSum x U l,B.quiet_of_hasSum x U b,add_zero])
      (L.quiet_of_hasSum x U l) e M ep one old actual s
    have term (a : (parts (J)).Mode) (ha : a ∈ shards (J) s) :
        (a.val.card:ℝ)*e*(M+e)^a.val.card ≤ 3*e*(C+2)^3 := by
      have card : a.val.card≤3 := (WilsonCapturedPrimarySoftLoad.size ha).trans (by simpa using card_le_univ s.val)
      have pow := (pow_le_pow_right₀ one card).trans (pow_le_pow_left₀ (zero_le_one.trans one)
        (by dsimp only [M];linarith : M+e≤C+2) 3)
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast card) ep) pow (by positivity) (by positivity)
    have sum := sum_le_sum term
    simp only [sum_const,nsmul_eq_mul] at sum
    refine gg.trans (sum.trans ?_)
    dsimp only [K]
    calc
      _ ≤ (Fintype.card (parts (J)).Mode:ℝ)*(3*e*(C+2)^3) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ (shards (J) s)) (by positivity)
      _ = _ := by ring
  rw [field]
  calc
    _ ≤ ∑ s, ‖c s * d s‖ := norm_sum_le ..
    _ ≤ ∑ s, (‖c s‖/Poly.toll w s)*K := sum_le_sum fun s _ => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left ((le_div_iff₀ (Poly.worth hw s)).mpr
        ((mul_comm (‖d s‖) _).le.trans (per s))) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := (sum_mul ..).symm

end YM.Integration.WilsonGeometricSignedClear
