import YM.Integration.WilsonCoherentJointReturn
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalTrial

/-! The numerical expansion of the same absolutely normalized compact word, including its
original engineering power, determines the independent finite forest coefficients. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalSeries
open Function Filter Lattice Wilson RG Tree Precision PertExtension PertExtension.Series
open RGComparison.Core16 FVA2 FVA2.CityHistory PhysicalNext.Repeat.Legato
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open scoped Classical Topology BigOperators

private theorem linear {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L:E→L[ℝ] F) {f:ℝ→E} {a:ℕ→E}
    (b:Tested.Aspiration f a):Tested.Aspiration (L ∘ f) (L ∘ a):=by
  intro n
  obtain ⟨C,hC,earned⟩:=b n
  refine ⟨‖L‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  filter_upwards [earned] with t ht
  have pass:Tested.peval (L ∘ a) n t=L (Tested.peval a n t):=by
    simp [Tested.peval,Zone.eval]
  change ‖L (f t)-Tested.peval (L ∘ a) n t‖≤_
  rw [pass,←map_sub]
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left ht (norm_nonneg L)).trans_eq (mul_assoc ..).symm)

theorem word {G:Gauge} {I:Type} [Fintype I] {c f:Side} (J:I→Spool.Lamp G) (S:StepData c f)
    (T:Forest S.ratio) {P:Parcel.Oven S.patch} (X:P.Form G) (Z:ChartRatio G)
    (u:Pins G c) (o:I→Site f) (large:Bid.Larger (G:=G) S) (b:S.Choices)
    (v:(Descent.nil (top:=f)).Tags) (ratio:LocalRatio Z) (paid:P.Offers X S.kernel)
    (inside:∀a,‖u a‖≤X.Q):
    Tested.Aspiration (Spool.reads J S u o) (WilsonCoherentJointReturn.series J S T Z u o large b v):=by
  rw [←WilsonCoherentJointReturn.same J S T Z u o large b v X ratio paid inside]
  have re:=linear Complex.ofRealCLM (Spool.forecast (X:=X) J o false paid large inside T ratio)
  have im:=linear (Complex.I • Complex.ofRealCLM) (Spool.forecast (X:=X) J o true paid large inside T ratio)
  convert re.add im using 1 <;> funext x <;> apply Complex.ext <;>
    simp [Function.comp_def,Spool.rank,Spool.look,Complex.I_mul]

def deposited (c:ℂ) (grade:ℕ) (a:ℕ→ℂ):ℕ→ℂ :=
  Tested.conv (fun n=>if n=grade then c else 0) a

theorem printed (c:ℂ) (grade:ℕ) {f:ℝ→ℂ} {a:ℕ→ℂ} (h:Tested.Aspiration f a):
    Tested.Aspiration (fun g=>c*((g:ℂ)^grade*f g)) (deposited c grade a):=by
  have placed:=(Tested.Aspiration.single c grade).prod h
  have eq:(fun g:ℝ=>c*((g:ℂ)^grade*f g))=(fun g:ℝ=>g^grade • c)*f:=by
    funext g
    simp [Complex.real_smul,mul_assoc,mul_left_comm]
  rw [eq]
  exact placed

theorem finite {T:Type*} [Fintype T] (c:T→ℂ) (grade:T→ℕ) (f:T→ℝ→ℂ) (a:T→ℕ→ℂ)
    (h:∀t,Tested.Aspiration (f t) (a t)):
    Tested.Aspiration (fun g=>∑t,c t*((g:ℂ)^(grade t)*f t g))
      (fun n=>∑t,deposited (c t) (grade t) (a t) n):=by
  have income:=Tested.Aspiration.sum Finset.univ _ _
    (fun t (_:t∈(Finset.univ:Finset T))=>printed (c t) (grade t) (h t))
  convert income using 1 <;> funext x <;> simp

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalSeries
