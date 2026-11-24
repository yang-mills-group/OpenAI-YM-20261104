import YM.Integration.WilsonThermometerUnitFilingCoverAudition
import YM.Integration.WilsonThermometerUnitFilingCoverTariff
import YM.Integration.WilsonThermometerUnitFilingCoverRadius

/-! Rooted Taylor wages on the genuine finite gauge field, with the original one-name salary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverInvoice
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open RegulatorIR Budget Budget.Packet Budget.Tuple Prim Profiles Halo WilsonOriginalPaidWalkCover
open WilsonThermometerUnitFilingJointMonomial WilsonThermometerUnitFilingCoverPieces
open WilsonThermometerUnitFilingPinnedIncome WilsonThermometerUnitFilingCoverAudition
open scoped Classical BigOperators ContDiff ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}{n N:Side}{o:Passport n Unit}{J:Census Unit}{I X:Type}
  (M:I→Row o J G X)(s:Finset I)(t:X)(ht:n.val∣N.val)(page:Fin (Pages n N))
  (a:ℂ→L[ℝ]ℝ) {S:Finset Cover} (included:WilsonThermometerUnitFilingCoverChart.Centered N S)
  {w:Unit→ℝ}{grades:Unit→ℕ}{σ C β δ:ℝ}{ord cap H:ℕ}
local notation "P"=>WilsonThermometerUnitFilingCoverChart.patch G S
local notation "B"=>bank M s t a
local notation "read"=>WilsonThermometerUnitFilingCoverChart.script S (B)
local notation "site"=>locus ht page o
local notation "port"=>WilsonThermometerUnitFilingCoverPort.branch included (site) G
local notation "data"=>WilsonThermometerUnitFilingPinnedIncome.envelope ht (pieces M s) page t 0

def directions (k:ℕ):Tuple (Option (↥(P))) k ↪ Tuple (WilsonEmittedRootedJetWage.Slot G N) k where
  toFun z:=Option.map (port) ∘ z
  inj':=by
    intro f g e;funext i
    have h:=congrFun e i
    change Option.map (port) (f i)=Option.map (port) (g i) at h
    cases hf:f i <;> cases hg:g i <;> simp_all

def invoice (G:Gauge)(k u:ℕ)(δ β C w:ℝ):ℝ:=
  (3+8*(k:ℝ))^u*WilsonThermometerUnitFilingMomentSale.price G k u δ*β^δ*C/w

private theorem settle {f h p w scale income:ℝ}(positive:0 < w)(root:0 ≤ scale)
    (bill:w*f ≤ p*h*income):scale*f ≤ scale*p*h*income/w:=by
  apply (le_div_iff₀ positive).mpr
  calc
    _ = scale*(w*f):=by ring
    _ ≤ scale*(p*h*income):=mul_le_mul_of_nonneg_left bill root
    _ = _:=by ring

include ht page included in
theorem wages (stock:Scene.Armada M w grades σ C ord cap H)(seed:0<σ)(tiny:0<δ)
    (late:Real.exp 1≤β)(paid:Real.exp (σ⁻¹^2)≤β)(income:0<w ())(re:‖a‖≤1)
    (inside:∀ g,LocalOn S ((B) g))(k u:ℕ):
    ∑ z:Tuple (Option (↥(P))) k,
      WilsonThermometerUnitFilingCoverRoom.wage u (length z) (name z) *
        |WilsonThermometerUnitFilingJointTensor.entry (read) k z| ≤ invoice G k u δ β C (w ()):=by
  let d:=directions (G:=G) (o:=o) ht page included k
  have bill:=WilsonThermometerUnitFilingCoverPieces.wage M s ht page t stock seed tiny late paid k u (Finset.univ.map d)
  rw [Finset.sum_map] at bill
  have normalized (z:Tuple (Option (↥(P))) k):
      |WilsonThermometerUnitFilingJointTensor.entry (read) k z|≤‖WilsonOriginalJointDeckMotion.entry k (data) (d z)‖:=by
    rw [paired M s t ht page a included inside]
    rw [abs_mul,abs_of_nonneg (by positivity),← Real.norm_eq_abs]
    have roof:=a.le_opNorm (WilsonOriginalJointDeckMotion.entry k (data) (d z))
    have cut : (k.factorial:ℝ)⁻¹≤1:=inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos k)
    calc
      _ ≤ 1 * ‖a (WilsonOriginalJointDeckMotion.entry k (data) (d z))‖:=mul_le_mul_of_nonneg_right cut (norm_nonneg _)
      _ ≤ ‖WilsonOriginalJointDeckMotion.entry k (data) (d z)‖:=by rw [one_mul];exact roof.trans (by
        simpa using mul_le_mul_of_nonneg_right re (norm_nonneg (WilsonOriginalJointDeckMotion.entry k (data) (d z))))
  let A:ℝ:=(3+8*(k:ℝ))^u
  have gross (z:Tuple (Option (↥(P))) k):WilsonThermometerUnitFilingCoverRoom.wage u (length z) (name z)
      ≤ A * premium ht page o u (d z):=WilsonThermometerUnitFilingCoverRadius.pricing included (site) z
  have estimate: (∑ z:Tuple (Option (↥(P))) k,
      WilsonThermometerUnitFilingCoverRoom.wage u (length z) (name z) *
        |WilsonThermometerUnitFilingJointTensor.entry (read) k z|)≤
      A* ∑ z:Tuple (Option (↥(P))) k,premium ht page o u (d z)*‖WilsonOriginalJointDeckMotion.entry k (data) (d z)‖:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum;intro z _
    rw [← mul_assoc]
    exact mul_le_mul (gross z) (normalized z) (abs_nonneg _) (by
      dsimp [A,premium]; positivity)
  exact estimate.trans (settle income (show 0≤A by dsimp [A];positivity) bill)

end YM.Integration.WilsonThermometerUnitFilingCoverInvoice
