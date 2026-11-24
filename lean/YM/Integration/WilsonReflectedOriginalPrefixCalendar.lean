import YM.Integration.WilsonReflectedOriginalPrefixTariff

/-! Cutoff-uniform fee for every two-root first occupation on a genuine run of
fine ancestors, including its source power, engineering transfer and hard rebate. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedOriginalPrefixCalendar
open Finset Lattice Wilson RG WilsonReflectedOriginalPrefixMesh WilsonReflectedOriginalPrefixTariff
open scoped BigOperators
variable {G:Gauge}(C:Calendar G)(p:ℕ)(q:∀i,Ratio (C.schedule.side i p) (C.schedule.side (i+1) p))
  (x y:∀i,Site (C.schedule.side i p))

def corridor (B D:ℕ):ℕ:=(D-2*B)/(4*B+2)

theorem legal {B D:ℕ}(ok:2*B≤D):corridor B D*(4*B+2)+2*B≤D:=by
  have h:=Nat.div_mul_le_self (D-2*B) (4*B+2)
  dsimp only [corridor];omega

theorem discount (B D:ℕ)(α:ℝ)(paid:1≤α):
    Real.exp (-(α*(corridor B D:ℝ)/8)) ≤ Real.exp (1/4)*Real.exp (-((D:ℝ)/(8*(4*B+2)))):=by
  have room:D≤(corridor B D+1)*(4*B+2)+2*B:=by
    have next: D-2*B < (corridor B D+1)*(4*B+2):=by
      apply (Nat.div_lt_iff_lt_mul (by omega:0<4*B+2)).mp
      exact Nat.lt_succ_self _
    omega
  have rr:(D:ℝ)≤((corridor B D:ℝ)+1)*(4*B+2)+2*B:=by exact_mod_cast room
  rw [←Real.exp_add];apply Real.exp_le_exp.mpr
  have pos:0<(8:ℝ)*(4*B+2):=by positivity
  have h: (D:ℝ)/(8*(4*B+2))≤(corridor B D:ℝ)/8+1/4:=by
    apply (div_le_iff₀ pos).mpr
    nlinarith only [rr,Nat.cast_nonneg (α:=ℝ) B]
  nlinarith only [h,mul_le_mul_of_nonneg_right paid (Nat.cast_nonneg (α:=ℝ) (corridor B D))]

private theorem geometric (t:ℕ):∑i∈range t,(1/2:ℝ)^i≤2:=by
  have eq:∑i∈range t,(1/2:ℝ)^i=2*(1-(1/2:ℝ)^t):=by
    induction t with
    | zero=>norm_num
    | succ t ih=>rw [sum_range_succ,ih,pow_succ];ring
  rw [eq];linarith only [pow_nonneg (by norm_num:0≤(1/2:ℝ)) t]

theorem original {K ages a b paidOrder:ℕ}(slope:0≤G.slopeConstant)(beg:1≤C.hatBeta K)
    (rx:∀i,K ≤ i → i<K+ages → (q i).parent (x (i+1))=x i)
    (ry:∀i,K ≤ i → i<K+ages → (q i).parent (y (i+1))=y i)
    (away:∃u:ℕ,reserve C K a b paidOrder 2 80≤(u:ℝ) ∧ u+2≤ separation (x K) (y K))
    (α:ℕ→ℝ)(source:∀i,K ≤ i → i<K+ages → 1≤α i):
    let B:=fun i=>⌈(Real.log (C.hatBeta i))^2⌉₊
    ∑t∈range ages,Real.exp (-(α (K+t)*(corridor (B (K+t)) (separation (x (K+t)) (y (K+t))):ℝ)/8))*
      (C.hatBeta (K+t))^a*((C.schedule.steps K t).val:ℝ)^b ≤
      2*Real.exp (1/4)*(C.hatBeta K)^(-(paidOrder:ℤ)):=by
  intro B
  obtain ⟨u,price,seats⟩:=away
  have earn t (live:t∈range ages):Real.exp (-(α (K+t)*(corridor (B (K+t)) (separation (x (K+t)) (y (K+t))):ℝ)/8))*
      (C.hatBeta (K+t))^a*((C.schedule.steps K t).val:ℝ)^b ≤
      (Real.exp (1/4)*(C.hatBeta K)^(-(paidOrder:ℤ)))*((1/2:ℝ)^t):=by
    have last:=mem_range.mp live
    have uv0:0≤Real.log ((C.schedule.steps K t).val:ℝ):=Real.log_nonneg (by exact_mod_cast (C.schedule.steps K t).property)
    have good:1≤C.hatBeta (K+t):=by rw [WilsonReflectedOriginalPrefixMesh.height C];linarith only [beg,mul_nonneg slope uv0]
    have roots:=rooted C.schedule p q x y K t u seats (fun i lo hi=>rx i lo (by omega)) (fun i lo hi=>ry i lo (by omega))
    have extent:reserve C K a b paidOrder 2 80*((C.schedule.steps K t).val:ℝ)≤ separation (x (K+t)) (y (K+t)):=by
      apply (mul_le_mul_of_nonneg_right price (Nat.cast_nonneg _)).trans
      exact_mod_cast roots
    have sp:0<blockBill C (K+t):=by unfold blockBill;positivity
    have cost:=salary C (by norm_num:0<(80:ℝ)) sp beg good (block C K t beg good) extent
    have hc:=discount (B (K+t)) (separation (x (K+t)) (y (K+t))) (α (K+t)) (source _ (by omega) (by omega))
    calc _ ≤ (Real.exp (1/4)*Real.exp (-((separation (x (K+t)) (y (K+t)):ℝ)/blockBill C (K+t))))*
          (C.hatBeta (K+t))^a*((C.schedule.steps K t).val:ℝ)^b :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg (zero_le_one.trans good) _)) (pow_nonneg (Nat.cast_nonneg _) _)
         _ = Real.exp (1/4)*_ := by ring
         _ ≤ Real.exp (1/4)*((C.hatBeta K)^(-(paidOrder:ℤ))*((1/2:ℝ)^t)) := mul_le_mul_of_nonneg_left cost (Real.exp_pos _).le
         _ = _ := by ring
  apply (sum_le_sum earn).trans
  rw [←mul_sum]
  have pos:0≤Real.exp (1/4)*(C.hatBeta K)^(-(paidOrder:ℤ)):=mul_nonneg (Real.exp_pos _).le (zpow_nonneg (zero_le_one.trans beg) _)
  exact (mul_le_mul_of_nonneg_left (geometric ages) pos).trans_eq (by ring)

end YM.Integration.WilsonReflectedOriginalPrefixCalendar
