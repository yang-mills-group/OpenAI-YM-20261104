import YM.Integration.WilsonFullFaceSignedUnit
import YM.Integration.WilsonThermometerCenteredWeight

/-! Restore the independently fixed inverse table in one signed scalar,
before dividing by the positive physical vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFullFacePooledUnit
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open Push.Local Planned.GuardedAtom Primitives.GCC.Anchor WilsonFiniteOrdinaryInverse
open WilsonThermometerCenteredAlgebra WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {X ι ν : Type} {o : Fin 3→Site n} {P : Rep G n}
local notation "J" => Stock.census (Fin 3)

theorem price (L : Lamps X ι G P.p o J) (B : Lamps X ν G P.p o J) (H : Hard X P.p P.activities.forced P.activities.K o J)
    (w : Fin 3→ℝ) (hw : ∀j,0<w j) {C e g : ℝ} (ep : 0<e) (low : e≤1) (cpos : 0≤C)
    (model : L.Paid w P.p.B (P.p.supportExponent+2) C) (debt : B.Paid w P.p.B (P.p.supportExponent+2) e)
    (x : X) (Q : Poly J) (gp : 0<g) (gs : g≤1) (loss : ℕ) (aperture : g^loss≤Poly.toll w full)
    (inverse : Poly.price (fun v=>g*w v) (inverseMass Q)≤fee J) :
    let A : Gallery X (ι⊕ν) o P J :=⟨L.join B,H⟩
    let t:ℂ:=(P.eval (1:Config G n):ℂ)
    ‖t⁻¹*((total (A.density x 1) Q).part full-t*(total (Poly.pass (bare L x 1)) Q).part full)‖ ≤
      fee (J)/g^(3+loss)*(e*WilsonFullFaceSignedPower.inter*((Fintype.card (parts (J)).Mode:ℝ)*(C+3)^3)) :=by
  intro A t
  let d (s:(J).Mode):=t⁻¹*((A.density x 1).part s-t*(Poly.pass (bare L x 1)).part s)
  have field : t⁻¹*((total (A.density x 1) Q).part full-t*(total (Poly.pass (bare L x 1)) Q).part full)=
      ∑s:(J).Mode,weight Q s*d s :=by
    rw [affine,affine,mul_sum,←sum_sub_distrib,mul_sum]
    apply sum_congr rfl
    intro s _
    dsimp only [d];ring
  let K:=e*WilsonFullFaceSignedPower.inter*((Fintype.card (parts (J)).Mode:ℝ)*(C+3)^3)
  have k0:0≤K:=mul_nonneg (mul_nonneg ep.le WilsonFullFaceSignedPower.bounded.choose_spec.1)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith only [cpos]) _))
  have per (s:(J).Mode) : ‖d s‖≤K/Poly.toll w s:=(le_div_iff₀ (Poly.worth hw s)).mpr <|
    (mul_comm ‖d s‖ (Poly.toll w s)).le.trans (WilsonFullFaceSignedUnit.priced L B H w hw ep low cpos model debt x s)
  have inv:=(WilsonThermometerCenteredWeight.original Q w hw gp gs loss aperture inverse)
  have bound : (∑s:(J).Mode, ‖weight Q s‖/Poly.toll w s)≤fee J/g^(3+loss) :=
    (le_div_iff₀ (pow_pos gp _)).mpr (by simpa only [mul_comm] using inv)
  rw [field]
  calc
    _ ≤ ∑s:(J).Mode,‖weight Q s*d s‖:=norm_sum_le ..
    _ ≤ ∑s:(J).Mode,(‖weight Q s‖/Poly.toll w s)*K :=sum_le_sum (fun s _=>by
      rw [norm_mul];exact (mul_le_mul_of_nonneg_left (per s) (norm_nonneg _)).trans_eq (by ring))
    _ = (∑s:(J).Mode,‖weight Q s‖/Poly.toll w s)*K:=(sum_mul ..).symm
    _ ≤ _:=mul_le_mul_of_nonneg_right bound k0

theorem nonneg_fee : 0≤fee J:=by
  unfold WilsonFiniteOrdinaryInverse.fee
  have r:0≤WilsonFiniteOrdinaryInverse.room J:=Finset.sum_nonneg fun i _=>by positivity
  exact Finset.sum_nonneg fun n _=>pow_nonneg (by linarith) n

theorem projected (τ g C e : ℝ) (loss : ℕ) (t0 : 0≤τ) (gp : 0<g) (low : g≤1)
    (e0 : 0≤e) (c0 : 0≤C) (cap : C≤2*(g⁻¹)^2) :
    τ*(fee J/g^(3+loss)*(e*WilsonFullFaceSignedPower.inter*
        ((Fintype.card (Multi.parts (J)).Mode:ℝ)*(C+3)^3))) ≤
    (τ*fee J*WilsonFullFaceSignedPower.inter*(Fintype.card (Multi.parts (J)).Mode:ℝ)*125)/g^(3+loss+6)*e:=by
  let x:=g⁻¹
  have t1 : 1≤x:=one_le_inv_iff₀.mpr ⟨gp,low⟩
  have cap0:C≤2*x^2:=cap
  have f0:=nonneg_fee
  have ip:=WilsonFullFaceSignedPower.bounded.choose_spec.1
  have sr : (C+3)^3 ≤ 125*x^6 :=calc
    _ ≤ (5*x^2)^3:=pow_le_pow_left₀ (by linarith only [c0]) (by linarith only [cap0,one_le_pow₀ t1 (n:=2)]) _
    _ = _:=by ring
  calc _ ≤ τ*(fee J/g^(3+loss)*(e*WilsonFullFaceSignedPower.inter*
          ((Fintype.card (Multi.parts (J)).Mode:ℝ)*(125*x^6)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
         (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left sr (Nat.cast_nonneg _)) (mul_nonneg e0 ip))
         (div_nonneg f0 (pow_nonneg gp.le _))) t0
       _ = _:=by dsimp only [x];rw [pow_add];ring

end YM.Integration.WilsonFullFacePooledUnit
