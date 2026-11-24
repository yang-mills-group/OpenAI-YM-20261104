import YM.Integration.WilsonMatrixOriginalDeckRawGrid
import YM.Integration.WilsonMatrixOriginalDeckFiled

/-! The full Wilson two-field regulator reading, with its actual disconnected part isolated on the same law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckRawMoment
open Filter Set Finset MeasureTheory Spec Table Ward PhysMS RG17 Lattice Wilson RG MS MS.Menus MS.Local.Physical
open Extraction Extraction.Order PhysicalNext.Repeat.Legato Next.UVStress Push.GridApprox OPE OPE.Therm
open WilsonMatrixOriginalDeckRawPanel
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Spec.Final R.family f S) (L:Layout F)
variable (h:ℕ) {B:Deck G} (Q:MS.Land.Prescription B)

abbrev SiteField (N p:ℕ):=Site (R.family.side N p)→ Config G (R.family.side N p)→ℂ

def deposited (r:ℝ)(w:R.family.label h)(N p:ℕ):SiteField R N p:=
  fun o=>R.family.O N p (atRef L h r (N,p) w) o

def joint (T:Test 2) (N p:ℕ) (ν:Measure (Config G (R.family.side N p))) (X Y:SiteField R N p):ℂ:=
  ∑x:Var R.family.S 2 N p,WilsonExternalMeshMass.charge R.family T x*(∫U,X (x 0) U*Y (x 1) U ∂ν)

def separatedMeans (T:Test 2) (N p:ℕ) (ν:Measure (Config G (R.family.side N p))) (X Y:SiteField R N p):ℂ:=
  ∑x:Var R.family.S 2 N p,WilsonExternalMeshMass.charge R.family T x*((∫U,X (x 0) U ∂ν)*(∫U,Y (x 1) U ∂ν))

theorem continuousRaw (N p:ℕ)(a:Glyph B h→ℂ)(t:ℝ)(k:ℕ)(o:Site (R.family.side N p)):
    Continuous (WilsonMatrixOriginalDeckRawPanel.registered R Q h N p a t k o):=by
  unfold WilsonMatrixOriginalDeckRawPanel.registered WilsonMacroscopicRichOriginalPortfolio.observation
  apply continuous_finsetSum;intro i _;apply continuous_const.mul
  apply continuous_finsetSum;intro j _;exact continuous_const.mul (R.family.continuousO ..)

theorem raw (T:Test 2) (N p:ℕ) (ν:Measure (Config G (R.family.side N p))) (a b:Glyph B h→ℂ)(t s:ℝ)(k l:ℕ):
    joint R T N p ν (WilsonMatrixOriginalDeckRawPanel.registered R Q h N p a t k) (WilsonMatrixOriginalDeckRawPanel.registered R Q h N p b s l)=
      WilsonMatrixOriginalDeckRawGrid.observed R Q h T N p ν a b t s k l+
        separatedMeans R T N p ν (WilsonMatrixOriginalDeckRawPanel.registered R Q h N p a t k) (WilsonMatrixOriginalDeckRawPanel.registered R Q h N p b s l):=by
  unfold joint WilsonMatrixOriginalDeckRawGrid.observed separatedMeans connected
  rw [←sum_add_distrib];apply sum_congr rfl;intro i _;ring

theorem original (g:Test 2) {r:ℝ}(hr:0<r)(s:ℝ)(w v:R.family.label h)(z:ℕ×ℕ):
    WilsonMatrixOriginalDeckFiled.operand R F L h g hr s w v z=
      joint R (dilate hr g) z.1 z.2 (scene R.family.path z.1 z.2 z.1)
        (deposited R F L h r w z.1 z.2) (deposited R F L h s v z.1 z.2):=by
  unfold WilsonMatrixOriginalDeckFiled.operand WilsonMatrixOriginalDeckRegulated.reading smears joint
  rw [mul_sum];apply sum_congr rfl;intro x _
  unfold WilsonExternalMeshMass.charge;rw [mul_assoc];congr 1;congr 1
  rw [R.family.num];change moment (R.family.beta z.1 z.2) _ = _
  rw [onstage (H:=R.family.path) (N:=z.1) (p:=z.2) R.makes.wilson];swap
  · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (R.family.continuousO ..).mul (R.family.continuousO ..)
  unfold moment;apply integral_congr_ae;filter_upwards with U
  rw [Fin.prod_univ_two];rfl

end YM.Integration.WilsonMatrixOriginalDeckRawMoment
