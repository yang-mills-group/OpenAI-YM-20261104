import YM.SchemeConversionRG11.FirstW.Hart.Port
/-! Highest discrete curl is a closed co-closed Maxwell jet on E4. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology Maxwell Next.Rank.CellsInt Tensor
open scoped BigOperators Classical ContDiff
open Push.FiniteDetection.Free.Hyper hiding flip pull
variable {E : Type*} [NormedAddCommGroup E] {G : Gauge} {j k : ℕ}
lemma curl_degree (A : Nu G (k+1)) (i j:Axis) : curlK A.val i j∈Loft _ k := by
  rw [show _= up i (field4 j A.val)-up j (field4 i A.val) from funext (curl_axis A.val i j)]
  exact Submodule.sub_mem _ (loft_up (cabin_floor A.property j) i) (loft_up (cabin_floor A.property i) j)
lemma safe (A : Field4 G) : Secure (curlK A) := by
  constructor
  · intro i j; funext x; simp only [curl_axis,Pi.neg_apply]; abel
  intro i j k; funext x; unfold stepValue; simp only [curl_axis,Pi.add_apply,Pi.zero_apply,up]; rw [add_right_comm x (step j) (step i),add_right_comm x (step k) (step i),add_right_comm x (step k) (step j)]; abel
lemma lampDiv {A : Field4 G}(h:A∈cabin G k) (j : Axis) (x : Cover) : ∑ i:Axis, (curlK A i j x -curlK A i j (x-step i))=0 := by
  have he i : curlK A i j x - curlK A i j (x-step i)=
    (field4 j A (x+step i)+field4 j A (x-step i) - 2 • field4 j A x) - ((field4 i A (x+step j)-field4 i A (x+step j-step i)) - (field4 i A x-field4 i A (x-step i))) := by simp only [curl_axis,up]; rw [sub_add_cancel,show x-step i+step j=x+step j-step i from by abel     ]; abel
  simp_rw [he]; rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib (f:=fun i=>field4 i A (x+step j)-field4 i A (x+step j-step i))]; change atoneLap (field4 j A) x - (atoneDiv A (x+step j)-atoneDiv A x)=0
  simp only [h.2.1,h.2.2,Pi.zero_apply,sub_zero]
lemma dome (A : Field4 G) (hA:A∈cabin G k)(hc:∀ i k,curlK A i k∈ Loft _ j) : leaf j (curlK A)∈onShell _ j := by
  have hs:=sprout j (safe A); refine ⟨hs,?_⟩; intro b x
  cases j with
  | zero=>
    have hi (f : Tensor.T E4 G.Color 0) (a) : grad a (Tensor.diagonal f) x=0 := by
      rw [show Tensor.diagonal f=fun _=>Tensor.diagonal f 0 from funext fun _=>congrArg f (Subsingleton.elim ..)]
      simp [grad, YM.Analysis.D] -- name
    apply Finset.sum_eq_zero (fun i _=>hi ..)
  | succ n=>
    let P := leaf (n+1) (curlK A); let R (i : Axis) := (P i b).curryLeft (basis i)
    let F (i):= curlK A i b
    have hh (i) (t : Fin n→ Axis) : R i (basis∘ t)= (↑(n+1).factorial:ℝ)⁻¹ • jumps (n+1) (Fin.cons i t) (F i) 0 := by
       unfold R P; rw [ContinuousMultilinearMap.curryLeft_apply,leaf, show Fin.cons (basis i) (basis ∘ t)=basis ∘ Fin.cons i t from funext (fun i=>Fin.cases (by rfl) (fun _=>rfl) i),fertile]
    have he (i:Axis) (t : Fin n→Axis) : jumps (n+1) (Fin.cons i t) (F i) 0=jumps n t (fun x=> F i x-F i (x-step i)) 0 := by
       let D:=List.ofFn t; have hv := loft_up (hc i b) i
       have h1 := loft_scoped n 0 (up i (F i)) (by simpa only [Nat.zero_add] using hv) D List.length_ofFn
       have h2 := loft_basis h1 ((0:Cover)+ -step i)
       rw [steps, jumps_eq,jumps_eq,show (fun x=> F i x-F i (x-step i))=fun x:Cover=>up i (F i) (x+ - step i) from funext (fun x=>by simp only [up,neg_add_cancel_right,sub_eq_add_neg]),combine_shift]
       exact h2.symm
    have hu : ∑ i,R i=0 := by
       apply seedEq; intro t; simp only [sum_apply,hh,he,← Finset.smul_sum]
       simp_rw [jumps_eq]; let p (i : Axis) := fun x:Cover=> F i x-F i (x-step i); have eh : (∑ i,p i) = 0 := funext (fun x:Cover=> by rw [Finset.sum_apply]; exact lampDiv hA b x)
       change (↑(n+1).factorial:ℝ)⁻¹ • ∑ i,combine (List.ofFn t) (p i) 0=0
       rw [←Finset.sum_apply, ←sum_combine _ Finset.univ p,eh,combine_zero]; exact smul_zero _
    have hv i : grad i (Tensor.diagonal (P i b)) x=(n+1) • R i (fun _=>x) := differential_diagonal _ (hs.coeffSym i b) x _
    change ∑ i:Axis, grad i (Tensor.diagonal (P i b)) x=0; simp_rw [hv,← Finset.smul_sum]; rw [← sum_apply,hu,zero_apply,smul_zero]
end YM.RG11.FirstW
