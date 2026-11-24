import YM.Integration.WilsonOriginalNullPlacedCalibration

/-! Reinstall the emitted local primary on the original canonical graph.
The two projection-null banks preserve their own complete numerical hard
inventories. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedLanding
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
theorem original (i d:ℕ) (o : Site (R.family.side i per)) (simple:G.Simple) (entered:m ≤ i) (live:i ≤ N) (home:Opened R.family d i per)
    (ready:(eventually_atTop.mp (WilsonOriginalNullLanding.local_section R d simple)).choose ≤ i)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (P:Coefficient (F₀ d) (R.family.side i per)) (u:ℝ) (shape:P.Format o R.family.params (W i))
    (paid:P.remBound o (W i) (κ i) u) (head:(F₀ d).coeffSize P.x ≤ u) :
    let α:=projection (F₀ d) R.family.params (W i).p.threshold o P
    let x:=(fitting d N per i R.makes home live).symm α
    let Y:=Drift.stamp o (Tour.placard R.family R.makes N per live o) ((R.family.factory d N per).entries i x)
    ∃ (v w:Coefficient (F₀ d) (R.family.side i per)) (e:ℝ),
      v.Format o R.family.params (W i) ∧ v.remBound o (W i) (κ i) u ∧
      projection (F₀ d) R.family.params (W i).p.threshold o v=0 ∧
      w.Format o R.family.params (P₀ i) ∧ w.remBound o (P₀ i) (safety R.family i) e ∧
      projection (F₀ d) R.family.params (P₀ i).p.threshold o w=0 ∧
      u+e ≤ (2+4*stock R.family i)*u ∧ (F₀ d).coeffSize α ≤ 2*u ∧
      projection (F₀ d) R.family.params (P₀ i).p.threshold o Y=α ∧
      Y.density o (S₀ d) (P₀ i)=(calValues (C:=R.family) d N per i x)∘translate o ∧
      P.density o (S₀ d) (W i)=v.density o (S₀ d) (W i)+
        w.density o (S₀ d) (P₀ i)+Y.density o (S₀ d) (P₀ i) := by
  intro α x Y
  have point:=(book.1.walk i entered live).truep.point
  have same := point.trans (R.makes.wilson.represents N per i live).vac.symm
  have dims:=dimensions d N per i R.makes home.post live
  obtain ⟨vf,vp,vn,_,price,actual⟩:=(eventually_atTop.mp (WilsonOriginalNullLanding.local_section R d simple)).choose_spec
    i ready per (W i) point o P shape paid head (by rw [same];exact dims.1) (by rw [same];exact dims.2)
    (by rw [point];exact fixed)
  obtain ⟨w,wf,wp,wn,_,_,yn,canonical,shifted⟩:=WilsonOriginalNullPlacedCalibration.original R.family R.makes d N per i home live o α
  let v:=WilsonMeasuredSectionCorrection.subtract (F₀ d) P α
  let e:=2*stock R.family i*(F₀ d).coeffSize α
  refine ⟨v,w,e,vf,vp,vn,wf,wp,wn,?_,price,yn,shifted,?_⟩
  · have col:0 ≤ stock R.family i:=le_trans zero_le_one (R.family.path.levels.params i).columns_ge
    have h:=mul_le_mul_of_nonneg_left price (mul_nonneg (show (0:ℝ)≤2 by norm_num) col)
    dsimp only [e];nlinarith only [h,rem_nonneg paid]
  · change P.density o (S₀ d) (W i)=v.density o (S₀ d) (W i)+(primary o α).density o (S₀ d) (W i) at actual
    rw [actual,WilsonOriginalNullPhysicalHistory.paid_primary R π Γ W book entered live d,canonical]
    abel

end YM.Integration.WilsonOriginalNullPlacedLanding
