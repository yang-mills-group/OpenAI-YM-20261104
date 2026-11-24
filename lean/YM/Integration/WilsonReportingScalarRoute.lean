import YM.Integration.WilsonReportingCellMoment
import YM.Integration.WilsonReportingUnitCells

/-! A scalar original field, inserted in any angular slot, remains a scalar multiple of the
full Wilson density at every earlier date. Its coefficient is the actual normalized
moment on the finite reporting scene and still carries the original affine test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingScalarRoute
open Function Filter Finset MeasureTheory Lattice Wilson RG Source RG05Readout Address Native
open Trace.Physical Extra.Histories MergeProof Accent WilsonReportingCellRoute WilsonReportingBareCell
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {d m N per b:ℕ}
variable {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d}

private def Shape (C:Family G) (N per j:ℕ) (F:Body→Goods G (C.side j per)):Prop :=
  ∀φ, ∃z:ℂ,F φ=z • liftVac C.path N per j

private theorem seed (h:C.Makes) (starts:∀e ≤ d,C.ref e ≤ N) (t:Letter d) (x:C.label (kept t))
    (z:ℂ) (constant:C.O N per x 0=fun _=>z) :
    Shape C N per N (pulseOut (basisTop C d N per (chunk t ((C.factory (kept t) N per).terminal.symm x)))) := by
  intro φ
  refine ⟨(readJ t 0 φ*(C.S.a N:ℂ)^(kept t))*z,?_⟩
  funext X
  have entered:=incidence h t φ (0:Site (C.side N per)) x
  have neutral (g:Goods G (C.side N per)):stepUp (1,false) 0 g=g:=Motion.dance_nil g
  rw [neutral,constant] at entered
  have rhs:=congrFun entered X
  change (basisTop C d N per (chunk t ((C.factory (kept t) N per).terminal.symm x)) φ).1 X=_
  rw [basis_agrees C d N per h starts φ X]
  rw [rhs]
  change ((C.path.rep N per N).eval X:ℂ)*(_*z)=(_*z)*((C.path.rep N per N).eval X:ℂ)
  ring

private theorem next (h:C.Makes) (live:m<N) {F:Body→Goods G (C.side (m+1) per)}
    (fromFine:Shape C N per (m+1) F) : Shape C N per m (journey C per m N d F) := by
  intro φ
  let pullTest (i:Bud C per m):=Native.pull (displacement C per m i) ((C.S.block m).val:ℝ)⁻¹ φ
  choose z hz using fun i:Bud C per m=>fromFine (pullTest i)
  let c(i:Bud C per m):ℂ:=((C.S.block m).val:ℂ)^d*z i
  have fine(i:Bud C per m): F (pullTest i) ∘ Lattice.pull (1:Signed) (child C per m i)=
      z i • liftVac C.path N per (m+1):=by
    rw [hz i]
    funext X
    exact congrArg (fun a:ℂ=>z i*a) (vac_pull C.path N per (m+1) h.wilson live _ _ X)
  have flow(i:Bud C per m):blast C.path N per m d (F (pullTest i) ∘ Lattice.pull (1:Signed) (child C per m i))=
      c i • liftVac C.path N per m:=by
    rw [fine i]
    have lin:blast C.path N per m d (z i • liftVac C.path N per (m+1))=
        z i • blast C.path N per m d (liftVac C.path N per (m+1)):=by
      unfold blast
      rw [StepData.push_smul _ _ _ _ (vac_integrable C.path N per (m+1) h.wilson live)]
      exact smul_comm _ _ _
    rw [lin,blast_vac _ _ _ _ _ h.wilson live,smul_smul,mul_comm (z i)]
  refine ⟨Address.average c,?_⟩
  change Address.average (fun i=>blast C.path N per m d (F (pullTest i) ∘ Lattice.pull (1:Signed) (child C per m i)))=_
  simp_rw [flow]
  unfold Address.average
  rw [←Finset.sum_smul,smul_smul,smul_eq_mul]

private theorem through (h:C.Makes) (q:ℕ) (live:m+q≤N) {F:Body→Goods G (C.side (m+q) per)}
    (top:Shape C N per (m+q) F) : Shape C N per m (route C per N d m q F) := by
  induction q with
  | zero => exact top
  | succ q ih => exact ih (by omega) (next h (by omega) top)

theorem density (h:C.Makes) (spine:Spine D B h b per d N V U) (starts:∀e ≤ d,C.ref e ≤ N)
    (t:Letter d) (x:C.label (kept t)) (z:ℂ) (constant:C.O N per x 0=fun _=>z)
    (beginning:b ≤ m) (live:m ≤ N) (φ:Body) :
    pulseOut (V m (Many.point U (chunk t ((C.factory (kept t) N per).terminal.symm x)) N m)) φ =
      WilsonReportingCellMoment.read t x m N per V U φ • liftVac C.path N per m := by
  obtain ⟨q,rfl⟩:=Nat.exists_eq_add_of_le live
  let y:=Many.point U (chunk t ((C.factory (kept t) (m+q) per).terminal.symm x)) (m+q) m
  have actual:=WilsonReportingCellRoute.bare h spine beginning (chunk t ((C.factory (kept t) (m+q) per).terminal.symm x))
  obtain ⟨a,ha⟩:=through (d:=d) h q le_rfl (seed h starts t x z constant) φ
  rw [actual] at ha
  have point (X:Config G (C.side m per)):Juniper.Caret.ratio (C.path.rep (m+q) per m) (pulseOut (V m y) φ) X=a := by
    rw [show pulseOut (V m y) φ=a • liftVac C.path (m+q) per m from ha]
    have pos:=Complex.ofReal_ne_zero.mpr (RG02.Actual.eval_pos h.wilson live X).ne'
    change a*((C.path.rep (m+q) per m).eval X:ℂ)/_=a
    field_simp [pos]
  haveI:IsProbabilityMeasure (OPE.Therm.scene C.path (m+q) per m):=OPE.Therm.probability h.wilson live
  have expected:WilsonReportingCellMoment.read t x m (m+q) per V U φ=a:=by
    unfold WilsonReportingCellMoment.read
    change (∫ X,Juniper.Caret.ratio (C.path.rep (m+q) per m) (pulseOut (V m y) φ) X ∂OPE.Therm.scene C.path (m+q) per m)=a
    simp_rw [point]
    simp
  rw [expected]
  exact ha

end YM.Integration.WilsonReportingScalarRoute
