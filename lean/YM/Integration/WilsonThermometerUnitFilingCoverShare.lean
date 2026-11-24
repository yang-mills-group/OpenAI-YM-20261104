import YM.Integration.WilsonThermometerUnitFilingCoverInvoice
import YM.Integration.WilsonThermometerUnitFilingCoverEra

/-! The captured finite cover report at its own opening carries the original group's rooted salary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverShare
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open RegulatorIR Taping Budget Budget.Packet Budget.Tuple Prim Profiles Halo Ledger Ledger.Sky
open WilsonThermometerUnitFilingCoverInvoice WilsonThermometerUnitFilingCoverAudition
open WilsonThermometerUnitFilingCoverRoom
open scoped Classical BigOperators ContDiff ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{o:Passport n Unit}{J:Census Unit}{I X:Type}
  (M:I→Row o J G X)(s:Finset I)(t:X)(a:ℂ→L[ℝ]ℝ)
  {w:Unit→ℝ}{grades:Unit→ℕ}{σ C β δ:ℝ}{ord cap H:ℕ}
  {W:Type}{stops:W→ℕ}{sides:Page stops→Side}{L:Heir sides G}
  (T:L.Accounts){h:ℕ}(F:W→Portrait G)(law:∀ x,LocalStamp (F x) h)

private theorem indices {Y:Type}(f:Figure Y→ℝ)(k r:ℕ)(p q:Fintype Y)(a b:DecidableEq Y):
    @WilsonThermometerUnitFilingJointTensor.card Y k p a (@WilsonThermometerUnitFilingJointTensor.entry Y p a f k) r =
    @WilsonThermometerUnitFilingJointTensor.card Y k q b (@WilsonThermometerUnitFilingJointTensor.entry Y q b f k) r:=by
  cases Subsingleton.elim p q
  cases Subsingleton.elim a b
  rfl

theorem patch_entry {h:ℕ} (B:Portrait G)(good:LocalStamp B h)(S:Finset Cover)
    (inside:∀ t,LocalOn S (B t))(e r:ℕ):
    WilsonThermometerUnitFilingCoverBasis.material B (WilsonThermometerUnitFilingCoverChart.resident B good S inside) h e r =
      offer (placeFin (WilsonThermometerUnitFilingCoverChart.patch G S))
        (WilsonThermometerUnitFilingJointTensor.card
          (WilsonThermometerUnitFilingJointTensor.entry (WilsonThermometerUnitFilingCoverChart.script S B) (e+h)) r):=by
  unfold WilsonThermometerUnitFilingCoverBasis.material
  apply congrArg (offer (placeFin (WilsonThermometerUnitFilingCoverChart.patch G S)))
  exact indices _ _ _ _ _ _ _

private theorem copy_price {Y Z:Type}{A:Tariff Z}(chart:Premium A)
    (inc:Y↪Z){k r:ℕ}(c:Tuple (Option Y) k→ℝ){p q:Fintype Y}{a b:DecidableEq Y}{funds:ℝ≥0∞}
    (offered:markQ chart (offer inc (@WilsonThermometerUnitFilingJointTensor.card Y k p a c r))≤funds):
    markQ chart (offer inc (@WilsonThermometerUnitFilingJointTensor.card Y k q b c r))≤funds:=by
  cases Subsingleton.elim p q
  cases Subsingleton.elim a b
  exact offered

theorem original (v:W)(matched:F v=bank M s t a)(stock:Scene.Armada M w grades σ C ord cap H)
    (seed:0<σ)(tiny:0<δ)(late:Real.exp 1≤β)(paid:Real.exp (σ⁻¹^2)≤β)(income:0<w ())(re:‖a‖≤1)
    {l ρ:ℝ}(hl:0<l)(hr:0<ρ)(safe:l≤ρ)(e r u:ℕ):
    markQ ((Premium.rooted (Tariff.native ρ hr u) 0).uses (plot (G:=G) l))
        ((WilsonThermometerUnitFilingCoverStock.report T F law).main (Page.opening stops v) e r)
      ≤ ENNReal.ofReal (invoice G (e+h) u δ β C (w ())):=by
  obtain ⟨S,inside⟩:=(law v).crown
  rw [WilsonThermometerUnitFilingCoverBasis.opening T F law v
    (WilsonThermometerUnitFilingCoverChart.resident (F v) (law v) S inside), patch_entry]
  rw [matched] at inside ⊢
  let src:=WilsonThermometerUnitFilingJointTensor.entry
    (WilsonThermometerUnitFilingCoverChart.script S (bank M s t a)) (e+h)
  have layout:=WilsonThermometerUnitFilingCoverTariff.charged src
    (placeFin (WilsonThermometerUnitFilingCoverChart.patch G S))
    (Premium.rooted (Tariff.native ρ hr u) 0) (plot (G:=G) l) r
    (wage (G:=G) (S:=S) u) (nonneg u) (perm u) (tariff hl hr safe u r)
  obtain ⟨N,ht,enclosed⟩:=WilsonThermometerUnitFilingCoverChart.periodic n S
  have many:0<Pages n N:=by
    have pos:0<N.val/n.val:=Nat.div_pos (Nat.le_of_dvd N.pos ht) n.pos
    unfold Pages;positivity
  have run:=wages M s t ht ⟨0,many⟩ a enclosed stock seed tiny late paid income re inside (e+h) u
  exact copy_price ((Premium.rooted (Tariff.native ρ hr u) 0).uses (plot (G:=G) l))
    (placeFin (WilsonThermometerUnitFilingCoverChart.patch G S)) src
    (layout.trans (ENNReal.ofReal_le_ofReal run))

end YM.Integration.WilsonThermometerUnitFilingCoverShare
