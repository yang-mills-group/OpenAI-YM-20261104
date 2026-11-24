import YM.Integration.WilsonIndependentCollarPaidWindingPanel
import YM.Integration.WilsonOriginalSparseFiledOpening

/-! Spend the full finite canonical source income before N and period, at the
actual physical station tolerance for all retained Taylor coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarStationPayment
open Filter Function Finset Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonIndependentCollarOriginalDose (axisFee)
open WilsonIndependentCollarOrbitalBasisPayment (Choices)
open WilsonIndependentCollarPaidWindingPanel (earned signed yield norm_signed)
open WilsonOriginalSparseFiledOpening (near)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open scoped Classical BigOperators Topology

variable {G:Gauge}{n:ℕ}{I:Type}[Fintype I][DecidableEq I]

theorem original (R:Run G)(simple:G.Simple)(k:Fin n→ℕ)(A:ℕ):
    let L:=R.family.path.levels
    ∃C:ℝ,0≤C ∧ ∀ᶠ m:ℕ in atTop,∀(K i:ℕ),m≤K →
      L.S.scale K-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀(target:(Stock.census (Fin n)).Mode)(M:Fin n→ℝ)(p power pole E:ℕ),
      let H:=R.alloy.B.a.clock.hatBeta (i+1)
      let bill:=earned R k A m C M target.val (Fintype.card I)
      0 < H →
      ∃ε:ℝ,0<ε ∧ ε=(H^(near power pole E))⁻¹/(1+max 0 bill) ∧
      ∀(N per:ℕ),K≤N → m+1≤N → ∀(v:(j:Fin n)→R.family.label (k j)),
      (∀j∈target.val,axisFee R k v j≤M j) →
      ∀(side:Side)(P:Passport side (Fin n))(B:I→Binder P (Stock.census (Fin n)))
        (x:Choices R k target.val→Affinity.Wallet (room (Fin n))),
      ∀(high low:ℕ→ℕ→Choices R k target.val→ℂ)(r d:ℕ),r≤p → d≤r →
      (∀a, ‖high r d a-low r d a‖≤ε*(∑s:Finset I,‖wages B (x a) target s‖)) →
      ‖(∑a,signed R k N per K m v target.val a*high r d a)-
        (∑a,signed R k N per K m v target.val a*low r d a)‖≤(H^(near power pole E))⁻¹:=by
  intro L
  obtain ⟨C,non,bought⟩:=WilsonIndependentCollarPaidWindingPanel.original (I:=I) R simple k A
  refine ⟨C,non,?_⟩
  filter_upwards [bought] with m paid
  intro K i newer span target M p power pole E H bill hot
  let goal:ℝ:=(H^(near power pole E))⁻¹
  let ε:=goal/(1+max 0 bill)
  have den:0<1+max 0 bill:=by linarith only [le_max_left 0 bill]
  have positive:0<ε:=div_pos (inv_pos.mpr (pow_pos hot _)) den
  refine ⟨ε,positive,rfl,?_⟩
  intro N per top base v money side P B x high low r d _ _ quote
  have sal:=paid K N per newer top base span target M v money side P B x
  let mass:=fun a=>yield R k N per K m v target.val a
  let gross:=fun a=>∑s:Finset I,‖wages B (x a) target s‖
  have fee(a:Choices R k target.val):0 ≤ mass a:=(norm_nonneg _).trans_eq (norm_signed R k N per K m v target.val a)
  calc
    _ = ‖∑a,signed R k N per K m v target.val a*(high r d a-low r d a)‖:=by rw [←sum_sub_distrib];simp only [mul_sub]
    _ ≤ ∑a,‖signed R k N per K m v target.val a*(high r d a-low r d a)‖:=norm_sum_le ..
    _ ≤ ∑a,ε*(mass a*gross a):=by
      apply sum_le_sum;intro a _
      rw [norm_mul,norm_signed]
      exact (mul_le_mul_of_nonneg_left (quote a) (fee a)).trans_eq (by change mass a*(ε*gross a)=_;ring)
    _ = ε*∑a,mass a*gross a:=(mul_sum ..).symm
    _ ≤ ε*bill:=mul_le_mul_of_nonneg_left sal positive.le
    _ ≤ ε*(1+max 0 bill):=mul_le_mul_of_nonneg_left (by linarith only [le_max_right 0 bill]) positive.le
    _ = goal:=div_mul_cancel₀ _ den.ne'

/-- Intersect the actual, separately nominated angular openings before the
period. Each reading may keep its own UV threshold after that period. -/
theorem through (p:ℕ)(opening:ℕ→ℕ→ℕ→Prop)
    (paid:∀ r≤p,∀ d≤r,∀ᶠ per:ℕ in atTop,opening r d per):
    ∀ᶠ per:ℕ in atTop,∀ r≤p,∀d≤r,opening r d per:=by
  have all:∀ᶠ per:ℕ in atTop,∀r:Fin (p+1),∀d:Fin (r.val+1),opening r.val d.val per:=
    eventually_all.2 fun r=>eventually_all.2 fun d=>paid r.val (by omega) d.val (by omega)
  filter_upwards [all] with per cap
  intro r smaller d below
  exact cap ⟨r,Nat.lt_succ_of_le smaller⟩ ⟨d,Nat.lt_succ_of_le below⟩

end YM.Integration.WilsonIndependentCollarStationPayment
end
