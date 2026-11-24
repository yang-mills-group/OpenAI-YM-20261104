import YM.Integration.WilsonLimitConstruction.FundedIndependentTestScaling
import YM.Integration.LocalComparisonModelIntegrable
import YM.Integration.NativePaidPacketColors
import YM.Integration.ActualPolynomialContraction

/-! Restore the original test envelopes mode by mode after measuring the
whole signed forecast correction. A marked component pays exactly the
product of the envelopes of its own occupied inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalRestoredMarkedBill

open Finset Lattice Wilson RG Marker Precision LocalComparison FullQLocal
open RG3.Script.Picnic
open WilsonLimitConstruction FundedIndependentTestScaling
open scoped Classical BigOperators

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}
    {D:V → ComparisonDensity.Address.Orbit} {n:Side} {A:Rep G n} {o:V→Site n}
    (T:Taste (TestSpace D) o A Γ) (HT:Multilinear D T) (Z:MarkedPackets D G n Γ)
    {p:BudgetPoint} {addr:V→Support n} {S:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {offset slope:ℕ}
    (paid:Z.Paid p addr S w g width budget offset slope) (hg:g≠0)

def error (x:TestSpace D) (U:Config G n) (ρ:ℂ) : Poly Γ :=
  ρ • (Poly.pass (Z.read x g U)*(T.leaf x).density U-(T.leaf x).density U)

include HT paid hg

theorem restored (cost:V→ℝ) (hc:∀v,0<cost v) (x:TestSpace D) (U:Config G n) (ρ:ℂ) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
      (error T Z (g:=g) (shrink cost x) U ρ)=error T Z (g:=g) x U ρ := by
  let P:=fun y=>Poly.pass (Z.read y g U)
  let H:=restoreEnvelope (R:=Γ) (envelopeProduct cost) (envelopeProduct_positive hc)
  have pub:= (paid.read_published U (fun y=>NativePaidPacketColors.read_summable paid hg y g U)).pass
  have model:H (P (shrink cost x))=P x:=by
    ext s
    change (envelopeProduct cost s:ℂ)*(P (shrink cost x)).part s=(P x).part s
    have h:(P (shrink cost x)).part s=(envelopeProduct cost s)⁻¹ • (P x).part s:=
      FundedIndependentTestScaling.row s (pub s) cost x
    rw [h,Complex.real_smul,Complex.ofReal_inv,←mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (envelopeProduct_positive hc s).ne'),one_mul]
  have actual:H ((T.leaf (shrink cost x)).density U)=(T.leaf x).density U:=by
    ext s
    change (envelopeProduct cost s:ℂ)*((T.leaf (shrink cost x)).density U).part s=_
    simpa only [Complex.real_smul] using (FundedIndependentTestScaling.restore T HT cost hc x U s).symm
  unfold error
  rw [map_smul,map_sub,restoreEnvelope_product_mul cost hc,model,actual]

theorem component (cost:V→ℝ) (hc:∀v,0<cost v) (x:TestSpace D) (U:Config G n) (ρ:ℂ)
    (s:Γ.Mode) {a:ℝ} (bill:Poly.price w (error T Z (g:=g) (shrink cost x) U ρ)≤a) :
    Poly.toll w s*‖(error T Z (g:=g) x U ρ).part s‖≤envelopeProduct cost s*a := by
  let small:=error T Z (g:=g) (shrink cost x) U ρ
  have coeff:=congrArg (fun b:Poly Γ=>b.part s) (restored T HT Z paid hg cost hc x U ρ)
  change (envelopeProduct cost s:ℂ)*small.part s=(error T Z (g:=g) x U ρ).part s at coeff
  rw [←coeff,norm_mul,Complex.norm_real,Real.norm_of_nonneg (envelopeProduct_positive hc s).le]
  calc
    _=envelopeProduct cost s*(Poly.toll w s*‖small.part s‖):=by ring
    _≤envelopeProduct cost s*a:=mul_le_mul_of_nonneg_left
      ((Poly.member paid.positive s small).trans bill) (envelopeProduct_positive hc s).le

end YM.Integration.QLocalRestoredMarkedBill
