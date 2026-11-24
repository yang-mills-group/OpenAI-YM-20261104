import YM.MSbar.Pole.Scale.Local

/-!
# Recursive MS-bar locality theorem, including arbitrary marks and tensor powers

Component lemma independent of incidence representation; causal comparison requires
verifying the differential RHS from actual diagram subintegrals. This lemma doesn't take
any subtraction at lower output weights at a smaller set of tensor directions.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin Curtain
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I] {k:ℕ} {Z : Type*}

/-- Pole algorithm step for a list of primitive terms, grouped before subtraction. -/
lemma local_sum (s : Finset Z) (l : Z → ℕ) (a:ℤ) (A : Finset I) (J K : Z → ℂ → Cloud I)
    (hK : ∀ i∈s, Vortex k (K i)) -- primitive pieces including analytic local vertices
    (h : ∀ i∈s,Pulse A ⟨a,l i⟩ (J i) (K i))
    (hg : ∀ r:ℝ,0<r→ Vortex 0 (∑ i∈s,roll A ⟨a,l i⟩ r (J i))) :
    ∃ M : ℕ→Cloud I,(∀ i, Local A a (M i)) ∧ (∀ r:ℝ,0<r→ Vortex 0 ((∑ i∈s,roll A ⟨a,l i⟩ r (K i))-purePolar k M)) := by
  let J' : ℝ→ ℂ→ Cloud I := fun r=> ∑ i∈s,roll A ⟨a,l i⟩ r (J i)
  let K' := ∑ i∈s, fun r=>roll A ⟨a,l i⟩ r (K i)
  have hh n x (r:ℝ)(hr:0<r):∀ᶠ z in approaching,
      HasDerivAt (fun t=>K' t z n x) ((r:ℂ)⁻¹*J' r z n x) r:=by
    filter_upwards [eventually_all_finset s|>.mpr (fun i hi=>h i hi)] with z hz
    unfold J' K'; simp_rw [Finset.sum_apply,Finset.mul_sum]; exact HasDerivAt.fun_sum fun i hi=>hz i hi n x r hr
  obtain ⟨C,H,hc⟩:= arrange s l a A hK
  change Soft (K'-polar k C) at hc
  have ht:= stiffness H hc hg hh
  let M i:= if i<k then C i 1 else 0
  refine ⟨M,fun i=>?_,fun r hr=>?_⟩
  · by_cases he:i<k
    · have hP (r) (hr:0<r): C i r=C i 1:= nailed H ht i he hr
      rw [show M i=C i 1 from if_pos he]; exact ⟨Spark.origin (H i) 1,fun ha=> funext fun n=>funext fun x=> (Spark.weights (H i) hP n x).1 ha, fun n x=> (Spark.weights (H i) hP n x).2⟩
    rw [show M i=0 from if_neg he]; exact Local.zero
  have hP:= hc.vortex r hr; change Vortex 0 (K' r - purePolar k (fun i => C i r)) at hP
  rw [show (∑ i∈s, roll A {a:=a,l:=l i} r (K i))=K' r by unfold K'; simp only [Finset.sum_apply], ext_cut _ _ (fun i=>C i r) (fun i hi=>?_)]
  · exact hP
  change (if i<k then _ else _)=_; rw [if_pos hi, nailed H ht i hi hr]

/-- Meromorphic primitive of an assigned edge-flow system. -/
lemma solved_mellin (s : Finset Z) (l : Z → ℕ) (a:ℤ) (A : Finset I) (J : Z → ℂ → Cloud I)
    (hJ : ∀ i∈s, Vortex k (J i)) (hf : ∀ i∈s,Wing A ⟨a,l i⟩ (J i))
    (hg : ∀ r:ℝ,0<r→ Vortex 0 (∑ i∈s,roll A ⟨a,l i⟩ r (J i))) :
    let F(i:Z):=step A ⟨a,l i⟩ (J i)
    ∃ M : ℕ→Cloud I,(∀ i, Local A a (M i)) ∧
      (∀ r:ℝ,0<r→ Vortex 0 ((∑ i∈s,roll A ⟨a,l i⟩ r (F i))-purePolar (k+1) M)) :=
    local_sum s l a A J _ (fun i hi=> beyond A _ (hJ i hi)) (fun i hi=> (currents A _ (hJ i hi) (hf i hi)).1) hg
end YM.MSbar.Pole
