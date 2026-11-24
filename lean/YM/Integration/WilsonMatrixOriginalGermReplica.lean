import YM.Integration.WilsonMatrixOriginalGermConditionalMask
import YM.Integration.WilsonRegisteredAxialConditional

/-! Two upper configurations given one fixed lower configuration are sampled
independently from the authentic iterated Wilson conditional. Their product
represents the exact remaining squared norm in the spring invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermReplica
open MeasureTheory ProbabilityTheory Filter Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalGermPanelRMS WilsonMatrixOriginalGermConditionalMask FVA2
open scoped BigOperators Classical ComplexConjugate
open private tested from YM.Integration.WilsonMatrixOriginalGermMaskPanel
variable {G:Gauge} (C:Family G) (N p j:ℕ)
local notation "cfg" k => Config G (C.side k p)

def history (m:ℕ) (live:m≤j):Kernel (cfg m) (cfg j):=
  Nat.decreasingInduction (motive:=fun m _=>Kernel (cfg m) (cfg j))
    (fun i _ K=>K ∘ₖ QLocalPhysicalPathKernel.next C N p i) Kernel.id live

theorem same:history C N p j j le_rfl=Kernel.id:=Nat.decreasingInduction_self ..
theorem advance {m:ℕ} (live:m<j):history C N p j m live.le=
    history C N p j (m+1) live ∘ₖ QLocalPhysicalPathKernel.next C N p m:=
  Nat.decreasingInduction_succ_left ..

theorem probability (made:C.Makes) (top:j≤N) {m:ℕ} (live:m≤j):IsMarkovKernel (history C N p j m live):=by
  induction live using Nat.decreasingInduction with
  | self=>rw [same];infer_instance
  | of_succ m h ih=>
    rw [advance C N p j h]
    letI:IsMarkovKernel (QLocalPhysicalPathKernel.next C N p m):=QLocalPhysicalPathKernel.isMarkov C made (h.trans_le top)
    letI:=ih
    infer_instance

theorem marginal (made:C.Makes) (top:j≤N) {m:ℕ} (live:m≤j):
    history C N p j m live ∘ₘ scene C.path N p m=scene C.path N p j:=by
  induction live using Nat.decreasingInduction with
  | self=>rw [same];simp
  | of_succ m h ih=>
    rw [advance C N p j h,←Measure.comp_assoc,QLocalPhysicalPathKernel.marginal C made (h.trans_le top),ih]

theorem actual (made:C.Makes) (top:j≤N) {X:(cfg j)→ℂ} (hX:Envelope X) {m:ℕ} (live:m≤j) (V:cfg m):
    (∫U,X U ∂history C N p j m live V)=actualTransport C (N:=N) X live V:=by
  induction live using Nat.decreasingInduction with
  | self=>rw [same,Kernel.id_apply,integral_dirac' X V hX.meas.stronglyMeasurable,actualTransport_base C made top]
  | of_succ m h ih=>
    let K:=history C N p j (m+1) h
    let A:=QLocalPhysicalPathKernel.next C N p m
    letI:IsMarkovKernel K:=probability C N p j made top h
    letI:IsMarkovKernel A:=QLocalPhysicalPathKernel.isMarkov C made (h.trans_le top)
    rw [advance C N p j h,actualTransport_step C made top X h]
    change (∫U,X U ∂(K ∘ₖ A) V)=_
    rw [Kernel.integral_comp (hX.integrableC _)]
    calc
      _=∫W,actualTransport C (N:=N) X h W ∂A V:=integral_congr_ae (Eventually.of_forall ih)
      _=_:=by
        rw [show A V=ActualWilsonConditionalRoots.fibre C (N:=N) V from QLocalPhysicalPathKernel.held C made (h.trans_le top) V]
        exact ActualWilsonConditionalRoots.average C made (h.trans_le top) V _

theorem copies (made:C.Makes) (top:j≤N) {X Y:(cfg j)→ℂ} (hX:Envelope X) (hY:Envelope Y) {m:ℕ} (live:m≤j) (V:cfg m):
    let K:=history C N p j m live V
    (∫pair,X pair.1*conj (Y pair.2) ∂K.prod K)=actualTransport C (N:=N) X live V*conj (actualTransport C (N:=N) Y live V):=by
  intro K
  letI:IsMarkovKernel (history C N p j m live):=probability C N p j made top live
  letI:IsProbabilityMeasure K:=inferInstanceAs (IsProbabilityMeasure (history C N p j m live V))
  calc
    _=(∫U,X U ∂K)*(∫U,conj (Y U) ∂K):=integral_prod_mul X (fun U=>conj (Y U))
    _=_:=by rw [integral_conj,actual C N p j made top hX live V,actual C N p j made top hY live V]

variable (R:Run G) {m k:ℕ} {N p:ℕ}

theorem measured (lower:m≤k) (upper:k≤N) (v:Fin 2→R.family.label 4) (φ:Test 2):
    let H:=panel R (p:=p) (lower.trans upper) v φ
    let K:=history R.family N p N k upper
    cost R (p:=p) lower upper v φ^2=
      ∫V,(∫pair,H pair.1*conj (H pair.2) ∂(K V).prod (K V)).re ∂scene R.family.path N p k:=by
  intro H K
  unfold cost
  rw [Real.sq_sqrt (integral_nonneg (fun U=>sq_nonneg _))]
  apply integral_congr_ae
  filter_upwards with V
  have here:=copies R.family N p N R.makes (le_refl N) (X:=H) (Y:=H) (tested R _ v φ) (tested R _ v φ) upper V
  change _=(∫pair,H pair.1*conj (H pair.2) ∂(K V).prod (K V)).re
  rw [here,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  rfl

end YM.Integration.WilsonMatrixOriginalGermReplica
