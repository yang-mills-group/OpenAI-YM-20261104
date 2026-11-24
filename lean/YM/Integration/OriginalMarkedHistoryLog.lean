import YM.Integration.OriginalMarkedPriceTransport
import YM.Integration.ManuscriptQLocalRawMaskCalendar

/-! The nonlinear connected response of two complete signed physical inputs
at any earlier scale of the same positive Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedHistoryLog
open Function Set Finset MeasureTheory Lattice Wilson RG Marker OPE.Therm Extra.Trajectories
open ManuscriptQLocalRegularConditional ManuscriptQLocalMeasuredMarkDifference
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    (C : Family G) (hC : C.Makes) {N p j m : ℕ} {w : V→ℝ} (hw : ∀i,0<w i)

def tariff (seeds power : ℕ) (B : ℝ) : ℝ :=
  let z := expBill seeds B
  let L := |logMod seeds z|
  (L*(2*z))^power*L*|expMod seeds B|

theorem nonnegative (seeds power : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ tariff seeds power B := by
  have hz : 0 ≤ expBill seeds B := Finset.sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (pow_nonneg hB i)
  exact mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hz)) _)
    (abs_nonneg _)) (abs_nonneg _)

omit [Fintype V] in
include hC hw in
theorem weighted (hj : j ≤ N) {F : Config G (C.side j p)→Poly Γ} {B : ℝ}
    (hF : Measurable F) (cap : ∀T,Poly.price w (F T) ≤ B) :
    Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _) := by
  obtain ⟨r,hr,norms⟩ := Poly.equivalent_norm (R:=Γ) hw
  have integrable : Integrable F (prior G _) := Integrable.of_bound hF.aestronglyMeasurable (B*r)
    (ae_of_all _ fun T=>(norms _).trans (mul_le_mul_of_nonneg_right (cap T) hr))
  exact Push.SectorMeasure.Env.smul_L1 ((C.path.rep N p j).envelope (hC.wilson.represents N p j hj).good) integrable

omit [Fintype V] in
include hw in
private theorem triangle (F Q : Poly Γ) : Poly.price w (F-Q) ≤ Poly.price w F+Poly.price w Q := by
  simpa only [sub_eq_add_neg,←neg_one_smul ℂ Q,Poly.adapted,norm_neg,norm_one,one_mul] using
    Poly.addition hw F (-Q)

include hC in
theorem observable (hj : j ≤ N) {F : Config G (C.side j p)→Poly Γ}
    (hF : Integrable (fun T=>(C.path.rep N p j).eval T • F T) (prior G _))
    (quiet : ∀T,(F T).part Γ.quiet=1) (hm : m ≤ j) :
    AEMeasurable (fun U=>connected (actualTransport C (N:=N) F hm U)) (scene C.path N p m) := by
  have move := actualScene_integrable_of_weighted C hC (hm.trans hj)
    (actualTransport_weighted_integrable_of_integrable C hC hj hF hm)
  have eqn : (fun U=>connected (actualTransport C (N:=N) F hm U))=
      fun U=>RG02.Marks.logTable (actualTransport C (N:=N) F hm U) := funext fun U=>
        RG02.Marks.connected_eq_logTable (OriginalMarkedPriceTransport.quiet C hC hj hF quiet hm U)
  rw [eqn]
  have polynomial : Continuous (fun t : Poly Γ=>RG02.Marks.logTable t) := by
    unfold RG02.Marks.logTable
    fun_prop
  exact polynomial.measurable.comp_aemeasurable move.aestronglyMeasurable.aemeasurable

include hC hw in
theorem received (hj : j ≤ N) (hm : m ≤ j) (X Y D E : Config G (C.side j p)→Poly Γ)
    (hX : Measurable X) (hY : Measurable Y) {B : ℝ}
    (capX : ∀T,Poly.price w (X T) ≤ B) (capY : ∀T,Poly.price w (Y T) ≤ B)
    (qx : ∀T,(X T).part Γ.quiet=0) (qy : ∀T,(Y T).part Γ.quiet=0)
    (hD : ∀T,D T=(C.path.rep N p j).eval T • Poly.pass (X T))
    (hE : ∀T,E T=(C.path.rep N p j).eval T • Poly.pass (Y T)) (power : ℕ) :
    let response := fun U=>Poly.price w (connected (actualSignedTransport C (N:=N) D hm U)-
      connected (actualSignedTransport C (N:=N) E hm U))
    Integrable (fun U=>(response U)^(power+1)) (scene C.path N p m) ∧
    ∫ U,(response U)^(power+1) ∂scene C.path N p m ≤
      tariff (Fintype.card V) power B*(∫ T,Poly.price w (X T-Y T) ∂scene C.path N p j) := by
  letI : IsProbabilityMeasure (scene C.path N p m) := probability (H:=C.path) (p:=p) hC.wilson (hm.trans hj)
  let F := fun T=>Poly.pass (X T)
  let Q := fun T=>Poly.pass (Y T)
  let z := expBill (Fintype.card V) B
  let L := |logMod (Fintype.card V) z|
  let K := |expMod (Fintype.card V) B|
  have hF : Measurable F := Poly.pass_cont.measurable.comp hX
  have hQ : Measurable Q := Poly.pass_cont.measurable.comp hY
  have fcap T : Poly.price w (F T) ≤ z := exp_price hw (capX T)
  have qcap T : Poly.price w (Q T) ≤ z := exp_price hw (capY T)
  have hp := weighted C hC hw hj hF fcap
  have hq := weighted C hC hw hj hQ qcap
  have hz : 0 ≤ z := (Poly.nonnegative hw (F 1)).trans (fcap 1)
  have hl : 0 ≤ L := abs_nonneg _
  let A := actualTransport C (N:=N) F hm
  let A' := actualTransport C (N:=N) Q hm
  let difference := fun U=>Poly.price w (A U-A' U)
  let response := fun U=>Poly.price w (connected (A U)-connected (A' U))
  have cA U : Poly.price w (A U) ≤ z :=
    ActualPolynomialContraction.transport_price_le C hC hw hj hF.aestronglyMeasurable fcap hm U
  have cA' U : Poly.price w (A' U) ≤ z :=
    ActualPolynomialContraction.transport_price_le C hC hw hj hQ.aestronglyMeasurable qcap hm U
  have non U : 0 ≤ difference U := Poly.nonnegative hw _
  have high U : difference U ≤ 2*z := (triangle hw (A U) (A' U)).trans
    (by simpa only [two_mul] using add_le_add (cA U) (cA' U))
  have root U : response U ≤ L*difference U := (ManuscriptQLocalMeasuredMarkDifference.connected hw
    (OriginalMarkedPriceTransport.quiet C hC hj hp (fun T=>Poly.pass_part _ (qx T)) hm U)
    (OriginalMarkedPriceTransport.quiet C hC hj hq (fun T=>Poly.pass_part _ (qy T)) hm U)
    (cA U) (cA' U)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (non U))
  have outI : Integrable difference (scene C.path N p m) := ActualPolynomialContraction.price_integrable w
    ((actualScene_integrable_of_weighted C hC (hm.trans hj)
      (actualTransport_weighted_integrable_of_integrable C hC hj hp hm)).sub
    (actualScene_integrable_of_weighted C hC (hm.trans hj)
      (actualTransport_weighted_integrable_of_integrable C hC hj hq hm)))
  have inI : Integrable (fun T=>Poly.price w (X T-Y T)) (scene C.path N p j) :=
    ActualPolynomialContraction.price_integrable w ((actualScene_integrable_of_weighted C hC hj
      (weighted C hC hw hj hX capX)).sub (actualScene_integrable_of_weighted C hC hj
      (weighted C hC hw hj hY capY)))
  have top : Integrable (fun T=>Poly.price w (F T-Q T)) (scene C.path N p j) :=
    ActualPolynomialContraction.price_integrable w ((actualScene_integrable_of_weighted C hC hj hp).sub
      (actualScene_integrable_of_weighted C hC hj hq))
  have after : ∫ U,difference U ∂scene C.path N p m ≤ ∫ T,Poly.price w (F T-Q T) ∂scene C.path N p j := by
    simpa only [OriginalMarkedPriceTransport.signed C hC hj hD hm,OriginalMarkedPriceTransport.signed C hC hj hE hm]
      using OriginalMarkedPriceTransport.comparison C hC hw hj hp hq hD hE hm
  have before : ∫ T,Poly.price w (F T-Q T) ∂scene C.path N p j ≤
     K*(∫ T,Poly.price w (X T-Y T) ∂scene C.path N p j) := by
    rw [←integral_const_mul]
    exact integral_mono top (inI.const_mul K) fun T=>(passing hw (capX T) (capY T)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Poly.nonnegative hw _))
  let factor := (L*(2*z))^power*L
  have hf : 0 ≤ factor := mul_nonneg (pow_nonneg (mul_nonneg hl (mul_nonneg (by norm_num) hz)) _) hl
  dsimp only
  rw [OriginalMarkedPriceTransport.signed C hC hj hD hm,OriginalMarkedPriceTransport.signed C hC hj hE hm]
  refine ⟨?_,?_⟩
  · have mA := observable C hC hj hp (fun T=>Poly.pass_part _ (qx T)) hm
    have mA' := observable C hC hj hq (fun T=>Poly.pass_part _ (qy T)) hm
    have meas : AEMeasurable response (scene C.path N p m) :=
      (Poly.price_cont w).measurable.comp_aemeasurable (mA.sub mA')
    apply Integrable.of_bound (meas.pow_const _).aestronglyMeasurable ((L*(2*z))^(power+1))
    refine ae_of_all _ fun U=>?_ 
    rw [Real.norm_of_nonneg (pow_nonneg (Poly.nonnegative hw _) _)]
    exact pow_le_pow_left₀ (Poly.nonnegative hw _) ((root U).trans (mul_le_mul_of_nonneg_left (high U) hl)) _
  calc ∫ U,(response U)^(power+1) ∂scene C.path N p m ≤ ∫ U,factor*difference U ∂scene C.path N p m := by
        apply integral_mono_of_nonneg (ae_of_all _ fun U=>pow_nonneg (Poly.nonnegative hw _) _) (outI.const_mul factor)
        refine ae_of_all _ fun U=>?_ 
        change (response U)^(power+1)≤factor*difference U
        rw [pow_succ]
        have bound := (root U).trans (mul_le_mul_of_nonneg_left (high U) hl)
        simpa only [factor,mul_assoc] using mul_le_mul
          (pow_le_pow_left₀ (Poly.nonnegative hw _) bound _) (root U) (Poly.nonnegative hw _)
          (pow_nonneg (mul_nonneg hl (mul_nonneg (by norm_num) hz)) _)
    _ = factor*(∫ U,difference U ∂scene C.path N p m) := integral_const_mul _ _
    _ ≤ factor*(K*(∫ T,Poly.price w (X T-Y T) ∂scene C.path N p j)) :=
      mul_le_mul_of_nonneg_left (after.trans before) hf
    _ = _ := by simp only [tariff,factor,z,L,K,mul_assoc]

end YM.Integration.OriginalMarkedHistoryLog
end
