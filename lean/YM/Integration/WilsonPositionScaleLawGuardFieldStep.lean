import YM.Integration.WilsonPositionScaleLawGuardCarry
import YM.Integration.WilsonPositionScaleLawGuardOffGrade

/-! The complete fixed original field obeys one MS scale evolution across both physical radii, including every lower coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardFieldStep
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize Asymptotics
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawGuardPhysical (expected)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGrade (grade)
open WilsonPositionScaleLawGuardCarry (term)
open scoped Topology Classical Asymptotics
theorem two {ι X:Type*}[NormedAddCommGroup X]{l:Filter ι}(v f:ι→X)(g:ι→ℝ)(small:v=o[l] g)(paid:∀i,‖f i‖≤2*‖v i‖):
    f=o[l] g:=by
  apply isLittleO_iff.mpr;intro ε hε
  filter_upwards [isLittleO_iff.mp small (half_pos hε)] with i fee
  exact (paid i).trans (by linarith only [fee])

theorem bounded (t:Ratio)(k:ℕ):‖1-(t.val:ℂ)^k‖≤2:=by
  have hp:=WilsonPositionScaleLawNative.positive t
  calc _≤‖(1:ℂ)‖+‖(t.val:ℂ)^k‖:=norm_sub_le _ _
       _≤2:=by rw [norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp];linarith only [pow_le_one₀ hp.le t.property.2 (n:=k)]

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
variable (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:∀q,WilsonPositionScaleLawGuardLittle.scale F J Z M ν d q)
include H funded law in
theorem engineering (q:ℕ)(O:S.Field d):
    (fun w:ℝ×Ratio=>physical F J Z d w.1 O-dressed Z F J d w.1 w.2 (physical F J Z d (w.2.val*w.1) O))=o[sweep] (fun w=>gθ w.1^q):=by
  let x(w:ℝ×Ratio):=physical F J Z d w.1 O
  let y(w:ℝ×Ratio):=physical F J Z d (w.2.val*w.1) O
  let U(w:ℝ×Ratio):=dressed Z F J d w.1 w.2
  let pieces(i:Fin (d+1))(w:ℝ×Ratio):=grade R.family i (x w)-grade R.family i (U w (y w))
  have each (i:Fin (d+1)):pieces i=o[sweep] (fun w=>gθ w.1^q):=by
    by_cases hi:i.val<d
    · have home:(fun w:ℝ×Ratio=>grade R.family i (x w))=o[sweep] (fun w=>gθ w.1^q):=(WilsonPositionScaleLawGuardOffGrade.row Z M H ν F J d funded law i hi q O).comp_tendsto tendsto_fst
      apply two _ _ _ home;intro w
      dsimp only [pieces,x,U,y]
      rw [WilsonPositionScaleLawGuardOrbit.step]
      let v:=grade R.family i (physical F J Z d w.1 O)
      change ‖v-(w.2.val:ℂ)^(d-i.val) • v‖≤2*‖v‖
      rw [show v-(w.2.val:ℂ)^(d-i.val) • v=(1-(w.2.val:ℂ)^(d-i.val)) • v by rw [sub_smul,one_smul],norm_smul]
      exact mul_le_mul_of_nonneg_right (bounded w.2 _) (norm_nonneg _)
    · have same:i.val=d:=by have:=i.isLt;omega
      apply isLittleO_iff.mpr;intro ε hε
      refine .of_forall fun w=>?_
      dsimp only [pieces,x,U,y]
      rw [WilsonPositionScaleLawGuardOrbit.step,same,Nat.sub_self,pow_zero,one_smul,sub_self,norm_zero]
      exact mul_nonneg hε.le (norm_nonneg _)
  have joined:=WilsonPositionScaleLawGuardOffGrade.finite Finset.univ pieces (fun w=>gθ w.1^q) (fun i _=>each i)
  apply joined.congr _ (fun _=>rfl)
  intro w;simp only [pieces,Finset.sum_sub_distrib,WilsonPositionScaleLawWhole.sumAll,x,U,y]

include H funded law in
theorem original:∃p:ℕ,∀q:ℕ,∀O:S.Field d,
    (fun w:ℝ×Ratio=>physical F J Z d w.1 O-
      expected F J Z M ν d (q+2*p) w.1 w.2 (physical F J Z d (w.2.val*w.1) O))=o[sweep] (fun w=>gθ w.1^q):=by
  obtain ⟨p,carry⟩:=WilsonPositionScaleLawGuardCarry.original Z M H ν F J d funded (law 2)
  refine ⟨p,?_⟩;intro q O
  have rest:=engineering Z M H ν F J d funded law q O
  apply (rest.add (carry q (law _) O)).congr _ (fun _=>rfl)
  intro w
  change (_-dressed Z F J d w.1 w.2 (physical F J Z d (w.2.val*w.1) O))+
    (dressed Z F J d w.1 w.2 (physical F J Z d (w.2.val*w.1) O)-_) = _
  abel

end YM.Integration.WilsonPositionScaleLawGuardFieldStep
