import YM.Integration.WilsonCoherentMayerSecondFiling
import YM.Integration.WilsonReportingPrescribedOldMicroscopic

/-! Independent tests projected at their own physical poses. An original marked push preserves
the absent modes, including when its Bochner integrand has no integral. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerSecondFaceTest
open Function MeasureTheory Finset Lattice Wilson RG Marker
open Source Labels Ac LocalComparison Global PhysicalNext.Repeat.Legato
open Comparison.Density.RenderM MergeProof.Accent FVA1 ComparisonDensity.Address
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V]

def projected (D:V→Orbit) (E:Finset V) (x:IndependentTests D):IndependentTests D:=
  fun v=>if v∈E then x v else ⟨0,(Orbit.Bill.zero (U:=D v)).more zero_le_one⟩

theorem away (D:V→Orbit) {E:Finset V} (x:IndependentTests D) {v:V} (absent:v∉E):
    testInclusion D (projected D E x) v=0:=by
  apply Subtype.ext
  simp only [projected,testInclusion,if_neg absent]
  rfl

theorem kept (D:V→Orbit) {E:Finset V} (x:IndependentTests D) {v:V} (inside:v∈E):
    testInclusion D (projected D E x) v=testInclusion D x v:=by
  apply Subtype.ext
  simp only [projected,testInclusion,if_pos inside]

variable [Fintype V] {G:Gauge} (R:Run G) {N per j n:ℕ}

local notation "Γ" => Stock.census V
local notation "K" => LocalComparison.actualPush R.family (R:=Γ) N per j

theorem silent (A:Config G (R.family.side (j+1) per)→Poly (Γ)) (s:(Γ).Mode)
    (zero:∀U,(A U).part s=0) (W:Config G (R.family.side j per)):
    (K A W).part s=0:=by
  let f:=fun U:Config G (R.family.side (j+1) per)=>
    (R.family.path.levels.clock.op j per).density (R.family.path.β N per (j+1)) U W • A U
  change (∫U,f U ∂prior G _).part s=0
  by_cases hi:Integrable f (prior G _)
  · change (Poly.get s) (∫U,f U ∂prior G _)=0
    rw [←(Poly.get s).integral_comp_comm hi]
    have empty:(fun U=>(Poly.get s) (f U))=0:=by
      funext U
      change (R.family.path.levels.clock.op j per).density (R.family.path.β N per (j+1)) U W • (A U).part s=0
      rw [zero U,smul_zero]
    rw [empty]; simp
  · rw [integral_undef hi]
    rfl

variable {B:MS.Local.Physical.Deck G} (Q:MS.Land.Prescription B) {hn:n≤j+1}
  (D:ActualRunQlocalNativeTuple.Datum R per (j+1) n hn V)
  (u:V→MS.Rake.Label B) (μ:ℝ) (order:V→ℕ)
local notation "d" => ActualRunQlocalNativeTuple.orbit D
local notation "group" => Config G (R.family.side (j+1) per)

theorem fresh (E:Finset V) (x:IndependentTests d) (U:group)
    (s:(Γ).Mode) (outside:¬s.val⊆E):
    (Poly.pass (Mach (Γ) (WilsonCoherentMayerSecondSource.operand Q D u μ order
      (testInclusion d (projected d E x)) U))).part s=0:=by
  obtain ⟨v,member,absent⟩:=Finset.not_subset.mp outside
  rw [Mach,Extra.Trajectories.pass_fire]
  apply Finset.prod_eq_zero member
  rw [WilsonCoherentMayerSecondSource.operand,away d x absent,map_zero,zero_mul]

theorem born [Nonempty V] (hG:G.Simple) (top:j+1≤N)
    (age:∀a:ActualOriginalQReaders.Slot u,R.family.ref a.2.size≤j+1)
    (E:Finset V) (x:IndependentTests d) (U:group) (s:(Γ).Mode) (outside:¬s.val⊆E):
    (((ActualOriginalQInput.input Q D u μ order hG N top).leaf
      (testInclusion d (projected d E x))).density U).part s=0:=by
  obtain ⟨v,member,absent⟩:=Finset.not_subset.mp outside
  rw [WilsonReportingPrescribedOldMicroscopic.stated R Q D u μ order hG top age]
  have empty:ActualStartupNormalizedQ.modeObservable Q D u μ order
      (testInclusion d (projected d E x)) s U=0:=by
    apply Finset.prod_eq_zero member
    rw [away d x absent,map_zero,zero_mul]
  rw [empty,smul_zero]

end YM.Integration.WilsonCoherentMayerSecondFaceTest
