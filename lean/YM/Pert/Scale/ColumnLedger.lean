import YM.Pert.Scale.Engineering
import YM.Pert.Scale.Attached
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Pert.Scale
open Labels Maxwell Extra.FD Position Set Function Analysis Topology Filter MeasureTheory RawLabels
open scoped ContDiff BigOperators
variable {G : Gauge} {F : Frames G} {C : Family G}
variable {e d n : ℕ}
section
variable (Q : Conditions F d n)
def swipe (v : Ledger Q × Buffer F d) : Ledger Q :=
  fun i z => decode Q v.1 (i:=i) (fun j=>motor F v.2 (baring F d (z j)))
lemma swipe_diff : ContDiff ℝ ω (swipe Q) := by
  refine contDiff_pi.mpr fun i=> contDiff_pi.mpr fun z=> ?_
  let u := fun j => baring F d (z j)
  have hz (i : Fin Q.slots) (v : inklet Q i) : ContDiff ℝ ω (fun g : Ledger Q => g i v) :=
      ((fun _ : ℝ→L[ℝ] ℝ => ContinuousLinearMap.contDiff (E:=inklet Q i → ℂ) (F:=ℂ) (n:=ω) (𝕜:=ℝ) (ContinuousLinearMap.proj (R:=ℝ) v)) 0).comp
       (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Ledger Q) (F:=inklet Q i→ℂ) (n:=ω) (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun j=>inklet Q j→ℂ) i))
  have ht (j : Slots (Q.arity i)) : ContDiff ℝ ω (fun g : Ledger Q×Buffer F d => motor F g.2 (u j)) := (motor_diff _).comp contDiff_snd
  apply ContDiff.sum (s:=Finset.univ) (f:=fun (k : inklet Q i) (v : Ledger Q × Buffer F d)=> (∏ j,(baring F d).coord (k j) (motor F v.2 (baring F d (z j)))) * v.1 i k)
  refine fun k _ => ContDiff.mul (contDiff_prod (fun j _ => ?_)) ((hz i k).comp contDiff_fst)
  let a := (LinearMap.toContinuousLinearMap (E:=E F d) (F':=ℂ) (((baring F d).coord (k j)).restrictScalars ℝ))
  exact (ContinuousLinearMap.contDiff a).comp (ht j)

private lemma singleBasis {i : Fin Q.slots} (p : Fin (Q.arity i) → E F d) (M : MultilinearMap ℂ (fun _ : Fin (Q.arity i) => E F d) ℂ) :
    (∑ k : inklet Q i, (Finset.univ.prod (fun j => (baring F d).coord (k j) (p j))) * M (fun j=>baring F d (k j)))=M p := by
  have ht (j : Fin (Q.arity i)) := (baring F d).sum_equivFun (p j)
  conv_rhs=>rw [←funext ht]
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]; refine Finset.sum_congr rfl fun z _ => ?_; rw [M.map_smul_univ]; rfl
end
variable (Q : Conditions C.labels d n)
lemma decode_profile (e : Ledger Q) (he : CleanProfiles Q) {i} (M : Points _ → MultilinearMap ℂ (fun _ : Fin (Q.arity i) => E C.labels d) ℂ)
   (hM : ∀ q, ContinuousOn (fun x => M x q) (conf _)) (hi : ∀ k, e i k = ∫ x : Points (Q.arity i), Q.profiles i x * M x (fun j=>baring C.labels d (k j))) (q) :
    decode Q e (i:=i) q = ∫ x : Points (Q.arity i), Q.profiles i x * M x q := by
  obtain ⟨t,ht⟩ := he i
  simp_rw [decode,hi,← ht]
  let a (k : inklet Q i) := ∏ j, (baring C.labels d).coord (k j) (q j)
  change (∑ k, a k * ∫ x : Points (Q.arity i), t x * M x (fun j=>baring C.labels d (k j))) = _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (f:=fun k x=> (a k)*((t x)*M x (fun j=>baring C.labels d (k j)))) (fun k _=> ?_)]
  · refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [mul_left_comm (_:ℂ) (t x),← Finset.mul_sum]
    exact congrArg (t x * ·) (singleBasis Q q (M x))
  exact (t.smearing (hM _)).const_mul _

variable (R : Conditions C.labels d n)
lemma swipe_wax (hR : CleanProfiles R) {t : ℝ} (ht : 0<t) :
   swipe R (wax R t,bank C.labels d t) = white R := by
  funext i z; let M := fun x : Points (R.arity i) => (freeTable C.labels).classMoment (freeTable C.labels) (fun _=>d) (t • x)
  have hm q : ContinuousOn (fun x : Points (R.arity i) => M x q) (conf _) :=
    (((freeTable C.labels).class_smooth _ (table_smooth _) (fun i=> ⟨d,q i⟩)).continuousOn).comp (ContinuousOn.const_smul continuousOn_id t) (fun _=> slides ht)
  unfold swipe
  rw [decode_profile R (wax R t) hR (i:=i) M hm (fun _=>rfl)]
  obtain ⟨f,hf⟩ := hR i
  refine integral_congr_ae (Filter.Eventually.of_forall fun x=> ?_)
  change R.profiles i x * Ward.disc (fun j=> (⟨d,_⟩:(freeTable C.labels).Tag)) (t • x) = R.profiles i x * _
  rw [← hf]
  by_cases hx : x∈tsupport f
  · refine congrArg (f x* ·) ?_
    simp only [Prod.snd, motor_bank,points_equ (f.tsupport_subset hx) _ ht.ne']
  simp [image_eq_zero_of_notMem_tsupport hx]
end YM.Pert.Scale
