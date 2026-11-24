import YM.Integration.WilsonMatrixOriginalDeckRawMoment

/-! Replace the two original dressed fields on the full Wilson Gram and retain both signed old partners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckRawComparison
open Filter Set Finset MeasureTheory Spec Table Ward PhysMS RG17 Lattice Wilson RG MS MS.Menus MS.Local.Physical
open Extraction Extraction.Order PhysicalNext.Repeat.Legato Next.UVStress Push.GridApprox OPE OPE.Therm
open WilsonMatrixOriginalDeckRawMoment
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {N p:ℕ} (T:Test 2)(ν:Measure (Config G (R.family.side N p)))
variable (X Y A B:SiteField R N p)

def due:ℂ:=∑x:Var R.family.S 2 N p,WilsonExternalMeshMass.charge R.family T x *
  (∫U,(X (x 0) U-A (x 0) U)*Y (x 1) U+A (x 0) U*(Y (x 1) U-B (x 1) U) ∂ν)

def income:ℝ:=∑x:Var R.family.S 2 N p,‖WilsonExternalMeshMass.charge R.family T x‖*
  (∫U,‖X (x 0) U-A (x 0) U‖*‖Y (x 1) U‖+‖A (x 0) U‖*‖Y (x 1) U-B (x 1) U‖ ∂ν)

variable [IsFiniteMeasure ν]
variable (cx:∀o,Continuous (X o))(cy:∀o,Continuous (Y o))(ca:∀o,Continuous (A o))(cb:∀o,Continuous (B o))
include cx cy ca cb in
theorem exact : joint R T N p ν X Y-joint R T N p ν A B=due R T ν X Y A B:=by
  unfold due joint;rw [←sum_sub_distrib];apply sum_congr rfl;intro x _;rw [←mul_sub];congr 1
  have xy:Integrable (fun U=>X (x 0) U*Y (x 1) U) ν:=((cx _).mul (cy _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ab:Integrable (fun U=>A (x 0) U*B (x 1) U) ν:=((ca _).mul (cb _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [←integral_sub xy ab]
  apply integral_congr_ae;filter_upwards with U;change X _ U * Y _ U-A _ U*B _ U=_;ring

include cx cy ca cb in
theorem price : ‖joint R T N p ν X Y-joint R T N p ν A B‖ ≤ income R T ν X Y A B:=by
  rw [exact R T ν X Y A B cx cy ca cb];unfold due income
  apply (norm_sum_le _ _).trans;apply sum_le_sum;intro x _;rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply norm_integral_le_of_norm_le
  · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (((cx _).sub (ca _)).norm.mul (cy _).norm).add ((ca _).norm.mul ((cy _).sub (cb _)).norm)
  · apply Eventually.of_forall;intro U;exact (norm_add_le _ _).trans_eq (by rw [norm_mul,norm_mul])

variable {f:Extraction.Order} {S:Table R.family.book} (F:Spec.Final R.family f S) (L:Layout F)
variable (h:ℕ) {D:Deck G} (Q:MS.Land.Prescription D)

/-- The same physical date, two actual `atRef` fields, and both full independently dressed candidate rosters. -/
theorem measured (g:Test 2){r:ℝ}(hr:0<r)(s:ℝ)(w v:R.family.label h)(z:ℕ×ℕ)
    (a b:Glyph D h→ℂ)(ta tb:ℝ)(k l:ℕ):
    let T:=dilate hr g
    let ν:=scene R.family.path z.1 z.2 z.1
    let X:=deposited R F L h r w z.1 z.2
    let Y:=deposited R F L h s v z.1 z.2
    let A:=WilsonMatrixOriginalDeckRawPanel.registered R Q h z.1 z.2 a ta k
    let B:=WilsonMatrixOriginalDeckRawPanel.registered R Q h z.1 z.2 b tb l
    let answer:=WilsonMatrixOriginalDeckFiled.operand R F L h g hr s w v z
    let nominal:=WilsonMatrixOriginalDeckRawGrid.observed R Q h T z.1 z.2 ν a b ta tb k l+separatedMeans R T z.1 z.2 ν A B
    answer-nominal=due R T ν X Y A B ∧ ‖answer-nominal‖ ≤ income R T ν X Y A B:=by
  dsimp only;rw [original R F L h g hr s w v z,←WilsonMatrixOriginalDeckRawMoment.raw]
  letI:IsProbabilityMeasure (scene R.family.path z.1 z.2 z.1):=probability R.makes.wilson le_rfl
  have hx:∀o,Continuous (deposited R F L h r w z.1 z.2 o):=fun _=>R.family.continuousO ..
  have hy:∀o,Continuous (deposited R F L h s v z.1 z.2 o):=fun _=>R.family.continuousO ..
  exact ⟨exact R _ _ _ _ _ _ hx hy (fun _=>continuousRaw R h Q ..) (fun _=>continuousRaw R h Q ..),
    price R _ _ _ _ _ _ hx hy (fun _=>continuousRaw R h Q ..) (fun _=>continuousRaw R h Q ..)⟩

end YM.Integration.WilsonMatrixOriginalDeckRawComparison
