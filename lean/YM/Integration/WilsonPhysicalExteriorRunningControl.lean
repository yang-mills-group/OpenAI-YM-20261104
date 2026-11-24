import YM.Integration.WilsonPhysicalExteriorRunningRows
import YM.Integration.MSCutoffGerms

/-! The same physical running substitution on observed cutoff-dependent
inputs. It preserves coefficientwise subexponential control on a
diverging genuine cutoff clock and leaves the numerical tree unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRunningControl
open Filter MS.Book MS.Book.Program FVAAlt2
open MSCutoffGerms WilsonPhysicalExteriorRunningRows
open scoped Topology BigOperators Classical
variable {I:Type} {l:Filter I} {t:I→ℝ}
local notation "PS" => PowerSeries ℂ

def Admitted (l:Filter I) (t:I→ℝ) (F:I→PS) : Prop :=
  ∀k,Moderate l t (fun i=>PowerSeries.coeff k (F i))

variable (ht:Tendsto t l atTop)
local notation "A" => functions ht

private def takeAt (i:I):A →+* ℂ := (Pi.evalRingHom (fun _:I=>ℂ) i).comp (functions ht).subtype

private def lift (F:I→PS) (allow:Admitted l t F):PowerSeries A :=
  PowerSeries.mk (fun k=>⟨fun i=>PowerSeries.coeff k (F i),allow k⟩)

private theorem value (F:I→PS) (allow:Admitted l t F) (i:I):
    PowerSeries.map (takeAt ht i) (lift ht F allow)=F i := by
  apply PowerSeries.ext;intro k
  rw [PowerSeries.coeff_map,lift,PowerSeries.coeff_mk]
  rfl

include ht in
private theorem working (P:Team) (μ:ℝ) : Admitted l t (fun i=>shift P (μ-t i)) := by
  intro k
  by_cases h:k=0
  · simp only [h,shift,PowerSeries.coeff_mk,if_true];exact convergent ht tendsto_const_nhds
  by_cases h':k=1
  · simp only [h',shift,PowerSeries.coeff_mk,one_ne_zero,if_false,if_true]
    exact convergent ht tendsto_const_nhds
  simp only [shift,PowerSeries.coeff_mk,if_neg h,if_neg h']
  exact MSCutoffGerms.polynomial ht μ _

private def variableAt (P:Team) (μ:ℝ):PowerSeries A :=
  lift ht (fun i=>shift P (μ-t i)) (working ht P μ)
private theorem base (P:Team) (μ:ℝ):PowerSeries.constantCoeff (variableAt ht P μ)=0 := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,variableAt,lift,PowerSeries.coeff_mk]
  apply Subtype.ext;funext i;exact share P _
private theorem leading (P:Team) (μ:ℝ):PowerSeries.coeff 1 (variableAt ht P μ)=1 := by
  rw [variableAt,lift,PowerSeries.coeff_mk];apply Subtype.ext;funext i;exact ann P _
private def before (P:Team) (μ:ℝ):PowerSeries A :=
  (variableAt ht P μ).substInvOfIsUnit (show IsUnit _ from (leading ht P μ).symm ▸ isUnit_one)
private theorem base_inv (P:Team) (μ:ℝ):PowerSeries.constantCoeff (before ht P μ)=0 := by
  simp [before]

private theorem reading (P:Team) (μ:ℝ) (F:PowerSeries A) (i:I) :
    PowerSeries.map (takeAt ht i) (PowerSeries.subst (variableAt ht P μ) F) =
      Lobby.redo P (μ-t i) (PowerSeries.map (takeAt ht i) F) := by
  have hm : PowerSeries.map (takeAt ht i) (PowerSeries.subst (variableAt ht P μ) F) =
      PowerSeries.subst (PowerSeries.map (takeAt ht i) (variableAt ht P μ))
        (PowerSeries.map (takeAt ht i) F) :=
    PowerSeries.map_subst (a:=variableAt ht P μ) (h:=takeAt ht i)
      (PowerSeries.HasSubst.of_constantCoeff_zero' (base ht P μ)) F
  rw [hm,variableAt,value,←WilsonPhysicalExteriorRunningRows.evaluated]
  exact (congrFun (PowerSeries.coe_substAlgHom ..) _).symm

include ht in
/-- Both signed positive orders and the true zeroth receiver on the
*same* original running team, after the change of bulk subtraction. -/
theorem measured (P:Team) (μ ν:ℝ) (F:I→PS) (allow:Admitted l t F) :
    Admitted l t (fun i=>reprice P (μ-t i) (ν-t i) (F i)) ∧
      ∀ i,PowerSeries.coeff 0 (reprice P (μ-t i) (ν-t i) (F i))=PowerSeries.coeff 0 (F i) := by
  let U:PowerSeries A:=lift ht F allow
  let G:PowerSeries A:=PowerSeries.subst (before ht P μ) U
  let Z:PowerSeries A:=PowerSeries.subst (variableAt ht P ν) G
  have un:PowerSeries.subst (variableAt ht P μ) G=U:=by
    change PowerSeries.subst _ (PowerSeries.subst (before ht P μ) U)=U
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (base_inv ht P μ))
      (PowerSeries.HasSubst.of_constantCoeff_zero' (base ht P μ)),before,
      PowerSeries.subst_substInvOfIsUnit_left _ (base ht P μ),PowerSeries.X_subst]
  have buy (i:I):PowerSeries.map (takeAt ht i) Z=reprice P (μ-t i) (ν-t i) (F i):=by
    change PowerSeries.map _ (PowerSeries.subst (variableAt ht P ν) G)=_
    rw [reading ht P ν G i,←WilsonPhysicalExteriorRunningRows.original P (μ-t i) (ν-t i),
      ←reading ht P μ G i,un,value]
  constructor
  · intro k
    have h:(fun i=>PowerSeries.coeff k (reprice P (μ-t i) (ν-t i) (F i)))=
        (PowerSeries.coeff k Z).val:=by
      funext i;rw [←buy,PowerSeries.coeff_map];rfl
    rw [h];exact (PowerSeries.coeff k Z).property
  · intro i
    have zero (w:ℝ) (a:PS): PowerSeries.coeff 0 (Lobby.redo P w a)=PowerSeries.coeff 0 a := by
      change PowerSeries.coeff 0 (PowerSeries.mk (Program.substitute (shift P w) (fun n=>PowerSeries.coeff n a)))=_
      rw [PowerSeries.coeff_mk,Program.pay0]
    rw [←buy]
    change PowerSeries.coeff 0 (PowerSeries.map _ (PowerSeries.subst (variableAt ht P ν) G))=_
    rw [reading ht P ν G i,zero]
    have old:=reading ht P μ G i
    rw [un,value] at old
    rw [old,zero]

end YM.Integration.WilsonPhysicalExteriorRunningControl
end
