import YM.Integration.SignedPostedMeasuredFields
import YM.Integration.SignedRegisteredMarkedProgram

/-! The selected original analytic run has one genuine formal chart, before every cutoff, period, forest, independent marked address, and actual mixed numerical Wick receiver. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedOriginalPostedCoefficient
open Function Filter Finset Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Matrix PowerSeries Bloch
open Comparison.RG02 Comparison.RG02.Cumulants PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} (R : Run G) (N m p : ℕ) (hm : m < N)
variable (forest₀ : Forest (R.family.path.levels.clock.op m p).ratio) (tag : (R.family.path.levels.clock.op m p).Choices)

include hm tag in
/-- The original native run supplies the complete heat coordinate projector on each actual forest with no new frame condition. -/
theorem frame : (extractV G (R.family.path.levels.clock.op m p) forest₀ (Bloch.installed (R.family.path.levels.clock.op m p).ratio (predictionA R.family.path.levels N m)))=reveal G (R.family.path.levels.clock.op m p) forest₀*((reveal G (R.family.path.levels.clock.op m p) forest₀).transpose*(extractV G (R.family.path.levels.clock.op m p) forest₀ (Bloch.installed (R.family.path.levels.clock.op m p).ratio (predictionA R.family.path.levels N m)))) := by
  apply sweeps G (R.family.path.levels.clock.op m p) forest₀ (Bloch.installed (R.family.path.levels.clock.op m p).ratio (predictionA R.family.path.levels N m)) (freeForms R.family.path.levels N m) (A:=freeForms R.family.path.levels N (m+1))
  · have pos := ((RunFormalChain.fromRun R).step N m p hm).hessian_pos forest₀ tag
    rw [OriginalMarkedHeatCovariance.precision R N m p hm forest₀ tag] at pos
    exact isUnit_iff_ne_zero.mpr pos.det_pos.ne'
  · exact horizon_step R.family.path.levels m N hm _ _ (R.family.path.levels.clock.op m p).sizes

private def probeCapture {A B : Type} (register : MvPolynomial A ℝ →+* MvPolynomial B ℂ)
    (scalars : ∀ (t : ℝ) h,register (t • h) = (t : ℂ) • register h)
    (Z : MvPolynomial B ℂ →ₗ[ℂ] ℂ) (ext : MvPolynomial B ℂ) (component : ℂ →L[ℝ] ℝ) : MvPolynomial A ℝ →ₗ[ℝ] ℝ where
  toFun h := component (Z (ext * register h))
  map_add' h k := by simp [map_add,mul_add]
  map_smul' t h := by
    rw [scalars,mul_smul_comm,map_smul]
    change component (t • Z (ext * register h))=t • component (Z (ext * register h))
    exact component.map_smul t _

/-- Genuine mixed complex physical Gaussian measurement against an arbitrary independent polynomial of all Gaussian variables and all externally fixed coarse directions. -/
def WickProbe (ext:Next.Rank.Normal.poly (Precision.Key forest₀ G)) (B : fieldDir G (R.family.side m p) 1) (component:ℂ→L[ℝ]ℝ) : POL (Active G forest₀⊕Woods G (R.family.side m p))→ₗ[ℝ]ℝ :=
  probeCapture (SignedRegisteredMarkedProgram.register forest₀ B)
    (fun z h=>by simp [Algebra.smul_def,SignedRegisteredMarkedProgram.register,MvPolynomial.algebraMap_eq])
    (Cloud.wick (((RunFormalChain.fromRun R).step N m p hm).covariance forest₀ tag) (((RunFormalChain.fromRun R).step N m p hm).symm forest₀ tag) 0) ext component

variable {i : ℕ} {k D:Fin i→ℕ} {e:ℕ} (Q:Realm G (e+1) Credit.leanC) (hq:Q.anchor ≤ m)

def OriginalField : Prop :=
  ∀ (J Z:Finset (Fin i)) (_:J⊆Z) (a:Fin i) (_:a∈J) (budget:ℝ) (_:0≤budget)
      (X:FundedMarkedPathSelection.Input Q hq Z k D budget) (y:Fin i→ Cover) (A₀:Case D) (b n:ℕ) (_:mass k J≤b) (_:n≤e)
      (ext:Next.Rank.Normal.poly (Precision.Key forest₀ G)) (B:fieldDir G (R.family.side m p) 1) (component:ℂ→L[ℝ]ℝ),
    let field:=FundedMarkedPathSelection.output X J N y
    let bank:=sphere field (mass k J) (e+1) a y
    let L:=WickProbe R N m p hm forest₀ tag ext B component
    SignedPostedMeasuredFields.expense (R.family.path.levels.clock.op m p) forest₀ (fderiv ℝ (((RunFormalChain.fromRun R).step N m p hm).b forest₀) 0) bank (e+1) A₀ (y a) b n L=
      L (coeff n (SignedMeasuredSourceSeries.probe (R.family.path.levels.clock.op m p) forest₀ (extractV G (R.family.path.levels.clock.op m p) forest₀ (Bloch.installed (R.family.path.levels.clock.op m p).ratio (predictionA R.family.path.levels N m))) (fderiv ℝ (((RunFormalChain.fromRun R).step N m p hm).b forest₀) 0) (flash (pPly A₀ J (fun j r=>plume (field.2 j r) (R.family.side (m+1) p))))))

/-- One original funded chart and price before every regulator, period, marked subset, geometry, original complex probe and finite perturbative order. The expectation operator inside the scalar probe uses this same run's Hessian, chosen tag and original covariance. -/
theorem on_run (R:Run G) (hG:G.Simple) (v:ℕ→ Gear G→ℝ) (paid:FundedMarkedCoverRows.prices v R.kit)
    (i:ℕ) (k D:Fin i→ℕ) (hk:∀a,k a<D a) (e:ℕ) : ∀ᶠ m:ℕ in atTop,
    ∃ Q:Realm G (e+1) Credit.leanC, Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.anchor=m ∧
    ∀ (N p:ℕ) (hm : m < N) (forest₀:Forest (R.family.path.levels.clock.op m p).ratio) (t:(R.family.path.levels.clock.op m p).Choices) (h:Q.anchor ≤ m),
      OriginalField (k:=k) (D:=D) R N m p hm forest₀ t Q h := by
  filter_upwards [FundedMarkedCoverRows.realm R hG v paid i k D hk e i (mass k univ)] with m hm'
  obtain ⟨Q,hQ,hO,_,hanchor,cl,ins,_,_⟩:=hm'
  refine ⟨Q,hQ,hO,hanchor,?_⟩
  intro N p hm forest₀ t h J Z hj a ha budget hfee X y A₀ b n hb hn ext B Φ
  have hJ : J.card ≤ i := by simpa using card_le_card (subset_univ J)
  have hmass : mass k J ≤ mass k univ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ J) (fun a _ _=>Nat.zero_le _)
  exact SignedPostedMeasuredFields.posted _ forest₀ _ _ X hj hfee hm cl i (mass k univ) hJ hmass ins a ha y
    (frame R N m p hm forest₀ t) (fderiv ℝ ((RunFormalChain.fromRun R).step N m p hm |>.b forest₀) 0).contDiff.contDiffAt (map_zero _) A₀ b n hb hn (WickProbe R N m p hm forest₀ t ext B Φ)

end YM.Integration.SignedOriginalPostedCoefficient
