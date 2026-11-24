import YM.Integration.WilsonPositionOriginalDiagnosticMeasuredGram

/-! Original positive-time tests admit the entire running finite
prescription, including every cutoff-dependent low field and its unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticPastSource
open Function Filter Set Finset MeasureTheory Lattice Wilson Cells RG
open PhysicalNext.Repeat.Legato Extraction Extraction.Order Extraction.Banks
open Spec Table Table.Pairing RG17 MS MS.Land MS.Local.Physical MS.Menus
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckPrescriptionFields
open WilsonPositionOriginalDiagnosticMeasuredGram WilsonPositionOriginalDiagnosticReflected
open WilsonPositionOriginalDiagnosticRightReading WilsonPositionOriginalDiagnosticRightAssay
open WilsonPositionOriginalDiagnosticRightSeries
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G)
local notation "C"=>R.family

def sample (φ:Test 1)(N per:ℕ): SiteField R N per →ₗ[ℂ] (Config G (R.family.side N per) → ℂ) where
  toFun X U:=∑o:Var R.family.S 1 N per,WilsonExternalMeshMass.charge R.family φ o*X (o 0) U
  map_add' X Y:=by funext U;simp [mul_add,sum_add_distrib]
  map_smul' c X:=by
    funext U
    change (∑o:Var R.family.S 1 N per,WilsonExternalMeshMass.charge R.family φ o*(c*X (o 0) U))=c*∑o:Var R.family.S 1 N per,WilsonExternalMeshMass.charge R.family φ o*X (o 0) U
    rw [Finset.mul_sum];apply sum_congr rfl;intro o _;ring

def sectionMap (d N per:ℕ): R.family.label d →ₗ[ℂ] SiteField R N per where
  toFun v o:= R.family.O N per v o
  map_add' x y:=by funext o;exact (R.family.linearO N per d o).map_add x y
  map_smul' c x:=by funext o;exact (R.family.linearO N per d o).map_smul c x

theorem single (d N per:ℕ)(a:Axis)(φ:Test 1)(ok:∀x∈tsupport φ,Points.allAbove a 0 x)
    (v:R.family.label d):
    sample R φ N per (sectionMap R d N per v)=stem C (oneTest R d a φ ok v) N per:=by
  funext U
  simp only [sample,sectionMap,LinearMap.coe_mk,AddHom.coe_mk,WilsonExternalMeshMass.charge,
    stem,base,oneTest,weightValue]
  apply sum_congr rfl;intro x _;congr 1
  change _=∏j:Fin 1,R.family.seen ⟨d,v⟩ (x j) U
  rw [Fin.prod_univ_one];rfl

private theorem grouped {n:Side}{K:Set (Site n)}{J:Type*}[Fintype J](A:J → Config G n → ℂ)
    (budget:∀j,Interior K (A j)):Interior K (∑j,A j):=by
  rw [show (∑j,A j)=(fun U=>∑j,A j U) by funext U;exact Finset.sum_apply ..]
  exact addRows univ fun j _=>budget j

theorem rows (f:Extraction.Order)(d:ℕ)(a:Axis)(φ:Test 1)(ok:∀x∈tsupport φ,Points.allAbove a 0 x):
    ∀ᶠi:ℕ×ℕ in f.fuse,∀v:R.family.label d,
      Interior (plane C i.1 i.2 a).sector (sample R φ i.1 i.2 (sectionMap R d i.1 i.2 v)):=by
  let e(k:(R.family.labels.level d).Index):R.family.label d:=Pi.single k 1
  have native(k):=kept C R.makes f (oneTest R d a φ ok (e k))
  filter_upwards [eventually_all.mpr native] with i pay
  intro v
  have expand:v=∑k:(R.family.labels.level d).Index,v k • e k:=by ext j;simp [e,Pi.single_apply]
  let A:= (sample R φ i.1 i.2).comp (sectionMap R d i.1 i.2)
  change Interior _ (A v)
  rw [expand,map_sum]
  apply grouped
  intro k
  rw [map_smul]
  apply Interior.scale
  exact (single R d i.1 i.2 a φ ok (e k)) ▸ pay k

private theorem filed {B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)(μ:ℝ)(p:ℕ)(g:ℂ)(N per:ℕ)(j:Glyph B h):
    submitted R Q h μ p g N per j=∑a:Glyph B h,((sources Q h μ p a j).eval g) •
      sectionMap R a.size N per (WilsonMacroscopicRichOriginalPortfolio.label R N per a):=by
  rw [fields]
  funext o U
  simp only [posted,WilsonMatrixOriginalDeckPrescriptionFields.raw,sectionMap,
    Finset.sum_apply,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul,mul_comm]

theorem prescribed {B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)(f:Extraction.Order)
    (a:Axis)(φ:Test 1)(ok:∀x∈tsupport φ,Points.allAbove a 0 x):
    ∀ᶠi:ℕ×ℕ in f.fuse,∀(μ ν:ℝ)(p:ℕ)(g:ℂ)(j:Glyph B h),Interior (plane C i.1 i.2 a).sector
      (sample R φ i.1 i.2 (remainder R Q h μ ν p g i.1 i.2 j)):=by
  filter_upwards [eventually_all.mpr fun b:Glyph B h=>rows R f b.size a φ ok] with i priced
  let V:=sample R φ i.1 i.2
  have entered(μ:ℝ)(p:ℕ)(g:ℂ)(j:Glyph B h):Interior (plane C i.1 i.2 a).sector
      (V (submitted R Q h μ p g i.1 i.2 j)):=by
    rw [filed,map_sum]
    apply grouped;intro b;rw [map_smul];exact Interior.scale _ (priced b _)
  intro μ ν p g j
  let O:=fun b=>submitted R Q h μ p g i.1 i.2 b
  let H:=submitted R Q h ν p g i.1 i.2 j
  let E:=fun b:Glyph B h=>(change Q h μ ν p b j).eval g
  have actual:remainder R Q h μ ν p g i.1 i.2 j=(∑b:Glyph B h,E b • O b)-H:=by
    funext o U
    simp only [remainder,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,E,O,H,mul_comm]
  rw [actual,map_sub,map_sum]
  rw [show ∀(x y:Config G (R.family.side i.1 i.2) → ℂ),x-y=x+(-1:ℂ) • y by intro x y;ext U;simp [sub_eq_add_neg]]
  apply Interior.plus
  · apply grouped;intro b;rw [map_smul];exact Interior.scale _ (entered μ p g b)
  · exact Interior.scale _ (entered ν p g j)

end YM.Integration.WilsonPositionOriginalDiagnosticPastSource
