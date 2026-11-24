import YM.Integration.WilsonOriginalNullCalibrated

/-! Reinstall the emitted local primary on the original canonical graph.
The two projection-null banks preserve their own complete numerical hard
inventories. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullJointLanding
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G:Gauge} (R:Run G) {m N per k:ℕ}
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (W:∀ j,Rep G (R.family.side j per))
  (book:Concourse R.alloy R.kit R.T π Γ m N per k W)
local notation "C₀" => R.family
local notation "P₀" j:max => R.family.path.rep N per j
local notation "F₀" d:max => R.family.labels.level d
local notation "S₀" d:max => R.family.localSection d
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j


include book in
theorem aligned (i d:ℕ) (simple:G.Simple) (entered:m ≤ i) (live:i ≤ N) (home:Opened R.family d i per)
    (ready:(eventually_atTop.mp (WilsonOriginalNullLanding.local_section R d simple)).choose ≤ i)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (P:Coefficient (F₀ d) (R.family.side i per)) (u:ℝ) (shape:P.Format 0 R.family.params (W i))
    (paid:P.remBound 0 (W i) (κ i) u) (head:(F₀ d).coeffSize P.x ≤ u) :
    let α:=projection (F₀ d) R.family.params (W i).p.threshold 0 P
    let x:=(fitting d N per i R.makes home live).symm α
    ∃ (v w:Coefficient (F₀ d) (R.family.side i per)) (e:ℝ),
      v.Format 0 R.family.params (W i) ∧ v.remBound 0 (W i) (κ i) u ∧
      projection (F₀ d) R.family.params (W i).p.threshold 0 v=0 ∧
      reads (C:=R.family) d N per i w e ∧ page (C:=R.family) d per i w=0 ∧
      u+e ≤ (2+4*stock R.family i)*u ∧ (F₀ d).coeffSize α ≤ 2*u ∧
      P.density 0 (S₀ d) (W i)=v.density 0 (S₀ d) (W i)+
        value (C:=R.family) d N per i w+calValues (C:=R.family) d N per i x := by
  intro α x
  have point:=(book.1.walk i entered live).truep.point
  have same := point.trans (R.makes.wilson.represents N per i live).vac.symm
  have dims:=dimensions d N per i R.makes home.post live
  obtain ⟨vf,vp,vn,_,price,actual⟩:=(eventually_atTop.mp (WilsonOriginalNullLanding.local_section R d simple)).choose_spec
    i ready per (W i) point 0 P shape paid head (by rw [same];exact dims.1) (by rw [same];exact dims.2)
    (by rw [point];exact fixed)
  obtain ⟨w,wallet,wn,canonical⟩:=WilsonOriginalNullCalibrated.aligned R.family d N per i R.makes home live α
  let v:=WilsonMeasuredSectionCorrection.subtract (F₀ d) P α
  let e:=2*stock R.family i*(F₀ d).coeffSize α
  refine ⟨v,w,e,vf,vp,vn,wallet,wn,?_,price,?_⟩
  · have col:0 ≤ stock R.family i:=le_trans zero_le_one (R.family.path.levels.params i).columns_ge
    have h:=mul_le_mul_of_nonneg_left price (mul_nonneg (show (0:ℝ)≤2 by norm_num) col)
    dsimp only [e];nlinarith only [h,rem_nonneg paid]
  · change P.density 0 (S₀ d) (W i)=v.density 0 (S₀ d) (W i)+(primary 0 α).density 0 (S₀ d) (W i) at actual
    rw [actual,WilsonOriginalNullPhysicalHistory.paid_primary R π Γ W book entered live d,canonical]
    abel

end YM.Integration.WilsonOriginalNullJointLanding
