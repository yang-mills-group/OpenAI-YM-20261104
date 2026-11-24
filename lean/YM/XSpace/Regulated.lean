import YangMills.WilsonProof.NativeSupport.YM.XSpace.OnShell
import YM.XSpace.Layout

/-!
# Formal correlation arrays at the large-even-side inversion quotient regulator

`g_N` variable here in every `PowerSeries`; common denominator, normalized before coefficient
reading. These are inputs to the position solves; they have not been re-expressed at a
measuring coupling yet. Centers and profiles in common length-one units, relative to a
point distant from all singular sites in the Euclidean metric of the given period. Formula
is asked on admitted compacts (large period relative to a fixed separated test, including
room for the microscopic field stencils); mesh-sampled on the top lattice using centered
integer lifts (see `Mesh.cover_window` about boundary of fundamental domain on those
compacts). Gives convenient multilinear function including on non-admitted supports too,
but such tests needn't make physical sense or be used for comparisons. This defines the
unpositioned arrays on all graded inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Filter Set Lattice Labels Source Maxwell MeasureTheory
open scoped Topology ContDiff BigOperators

structure Initialize (G : Gauge) where
  hol : Hol G
  surveys (d : ℕ) : Survey G hol d
  tree (p : Period): p.Tree

variable {G : Gauge} {n : ℕ}
namespace Initialize
variable (A : Initialize G) (p : Mesh)

def standard (G : Gauge) : Initialize G := by
  let H := Classical.choice (Hol.exists_ode G)
  exact ⟨H,fun d=> Classical.choice (YM.XSpace.surveys H d), Period.standardTree⟩

def atSite (d : ℕ) (x : p.Sites) : (On.Grade G d) →ₗ[ℂ] Bare.Series (A.tree p.p) G :=
    ((p.spacing:ℂ)^d)⁻¹ • On.stencil A.hol (A.surveys d) _ _ x

def atTuple (d : Fin n → ℕ) (x : Fin n → p.Sites) :=
  (Bare.normalized (A.tree p.p) G).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra ℂ (Fin n) (Bare.Series (A.tree p.p) G)).compLinearMap (fun i => A.atSite p (d i) (x i)))

lemma atTuple_eq (d : Fin n → ℕ) (x : Fin n → p.Sites) (v : ∀ i, On.Grade G (d i)) : A.atTuple p d x v=Bare.normalized _ G (∏ i, A.atSite p _ (x i) (v i)):= rfl

def report (d : Fin n → ℕ) : Test n→ₗ[ℂ] MultilinearMap ℂ (fun i => ↥(On.Grade G (d i))) (PowerSeries ℂ) where
  toFun t:= ((p.spacing:ℂ)^(4*n)) • ∑ x : Fin n→p.Sites, p.smear (lift ∘ x) t • A.atTuple p d x
  map_add' t u:=by simp [add_smul, Finset.sum_add_distrib, smul_add]
  map_smul' c t:=by simp only [map_smul,smul_assoc,RingHom.id_apply,Finset.smul_sum]; simp_rw [smul_comm c ((p.spacing:ℂ)^(4*n))]

lemma report_formula (d : Fin n → ℕ) (t : Test n) (v : ∀ i, On.Grade G (d i)) :
    A.report p d t v=((p.spacing:ℂ)^(4*n)) • ∑ x : Fin n→p.Sites,p.smear (lift ∘ x) t • A.atTuple p d x v:=by simp only [Initialize.report,LinearMap.coe_mk,AddHom.coe_mk,smul_apply,sum_apply]

lemma coefficient (d : Fin n → ℕ) (t : Test n) (v : ∀ i, On.Grade G (d i)) (m : ℕ) :
    PowerSeries.coeff m (A.report p d t v)= (p.spacing:ℂ)^(4*n) * (p.vol:ℂ)⁻¹ * ∫ c in p.Box,
      ∑ x : Fin n → p.Sites, t (p.rel (lift ∘ x) c)*PowerSeries.coeff m ((A.atTuple p d x) v) :=by
  rw [report_formula,map_smul,map_sum,mul_assoc,smul_eq_mul]; apply congr_arg
  change _ = _* ∫ c in p.Box, ∑ i : Fin n → p.Sites, p.termView t (lift ∘ i) c*PowerSeries.coeff m ((A.atTuple p d i) v)
  rw [integral_finsetSum _ (fun i _ => (p.term_integrable t (lift ∘ i)).mul_const _)]
  simp_rw [Finset.mul_sum, map_smul,Mesh.smear,LinearMap.coe_mk,AddHom.coe_mk, Complex.real_smul,smul_eq_mul,integral_mul_const,Complex.ofReal_inv, mul_assoc]
end Initialize
end YM.XSpace
