import YM.Trace.Fock.PairData
import Mathlib.Analysis.Calculus.Taylor
/-!
Point-support and finite jets in the spatial Schwartz testing used for the shell branch
with the Cauchy-data restriction.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option autoImplicit false
namespace YM.Trace.Shell
open Filter Set MeasureTheory Function Complex YM Boundary
open scoped Topology Pointwise ContDiff
abbrev pinOrders := Finset (ℕ × ℕ)
abbrev pinSize (s : pinOrders) (f : Probe Mom) := s.sup (schwartzSeminormFamily ℂ Mom ℂ) f
lemma pinSize_nonneg (k f) : 0 ≤ pinSize k f := apply_nonneg ..
lemma finite_price (n : ℕ) (T : Probe Mom →L[ℂ] Probe Mom) : ∃ k : pinOrders, ∃ c : NNReal, ∀ f : Probe Mom, orderCost (T f) n ≤ (c:ℝ) * pinSize k f := by
    let p (i:ℕ) := (SchwartzMap.seminorm ℂ (E:=Mom) (F:=ℂ) i 0).comp T.toLinearMap
    obtain ⟨s,C,hC,h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ Mom ℂ) (p 0 + p n) (by
       exact (continuous_orderCost n).comp T.continuous)
    exact ⟨s,C,h⟩
lemma pin_le (s : pinOrders) (C : ℝ) (f : Probe Mom) (hC : C≥0) (h : ∀ i∈s, Probe.size i.1 i.2 f ≤ C) : pinSize s f ≤ C := Seminorm.finset_sup_apply_le hC h

noncomputable def axis (i : SpaceAxis) : Mom := EuclideanSpace.single i (1:ℝ)
def jj (j : ℕ) (f : Probe Mom) (x : Mom) := ‖iteratedFDeriv ℝ j (⇑f) x‖
lemma product_j_ineq (f q : Probe Mom) (n : ℕ) (x):
   jj n (Probe.sew f q) x ≤ ∑ j∈Finset.range (n+1), ((Nat.choose n j):ℝ) * jj j f x * jj (n-j) q x := by
   unfold jj
   rw [show (⇑(Probe.sew f q) : Mom→ℂ)=_ from funext (Probe.sews f q)]; exact
     norm_iteratedFDeriv_mul_le (f.smooth (⊤:ℕ∞)) (q.smooth (⊤:ℕ∞)) x (show (↑n : ℕ∞ω) ≤ ↑(⊤:ℕ∞) by exact_mod_cast le_top)
lemma jj_nonneg k f x : 0 ≤ jj k f x := norm_nonneg _
lemma jj_le (k : ℕ) (f : Probe Mom) (x) : jj k f x ≤ Probe.size 0 k f := by exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ ..
abbrev multi_slots (n : ℕ) := Fin n→SpaceAxis
def monomialJet (n : ℕ) (k : multi_slots n) (x : Mom) (f : Probe Mom) := iteratedFDeriv ℝ n (⇑f) x (fun i=>axis (k i))
def FlatAns (q : ℕ) (n : Mom) (f : Probe Mom) := ∀ j ≤ q, ∀ k, monomialJet j k n f = 0

lemma sum_axis (x : Mom) : x = ∑ i:SpaceAxis, (x i) • axis i := by
     ext j; change x j = _
     change EuclideanSpace.proj j x=(EuclideanSpace.proj (ι:=SpaceAxis) (𝕜:=ℝ) j) (∑ i:SpaceAxis, (x i) • axis i)
     rw [map_sum]
     refine Eq.symm (Eq.trans (Finset.sum_eq_single j ?_ (by simp)) ?_)
     all_goals simp [map_smul,axis,eq_comm] <;> try grind
private lemma jets_zero {x : Mom} {f : Probe Mom} {k : ℕ} (hf : FlatAns k x f) {q} (hq : q≤k) : iteratedFDeriv ℝ q (⇑f) x = 0 := by
    let T : MultilinearMap ℝ (fun _ : Fin q=>Mom) ℂ := (iteratedFDeriv ℝ q (⇑f) x : ContinuousMultilinearMap ℝ _ ℂ).toMultilinearMap
    apply ContinuousMultilinearMap.ext (fun i:Fin q→Mom => show _ from ?_)
    change T i=0
    conv_lhs => erw [show i = _ from funext (fun j=> sum_axis (i j))]
    rw [T.map_sum (fun j r=> (i j r) • axis r)]
    simp_rw [T.map_smul_univ,show ∀ k:multi_slots q, T (fun j=>axis (k j))=0 from hf q hq, smul_zero,Finset.sum_const_zero]

private lemma jj_highBound (f : Probe Mom) (j N M : ℕ) (h : j+N+1≤M) (hz : FlatAns M 0 f)
    (hc : ∃ C ≥ 0, ∀ x:Mom, ‖x‖≤1 → jj (j+1) f x ≤ C*‖x‖^N) : ∃ C ≥ 0, ∀ x:Mom, ‖x‖≤1→ jj j f x ≤ C*‖x‖^(N+1) := by
    obtain ⟨C,hC,hb⟩:=hc
    let u := iteratedFDeriv ℝ j (⇑f)
    have eH (x) : ‖fderiv ℝ u x‖=jj (j+1) f x := by simp only [u,fderiv_iteratedFDeriv,jj, LinearIsometryEquiv.norm_map]; exact LinearIsometryEquiv.norm_map ..
    have hd : Differentiable ℝ u := (f.smooth (⊤:ℕ∞)).differentiable_iteratedFDeriv (by exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j))
    refine ⟨C,hC,fun x hX=> ?_⟩
    let K := Metric.closedBall (0:Mom) ‖x‖
    have HK : ∀ r ∈ K, ‖fderiv ℝ u r‖ ≤ C*‖x‖^N := fun r h => by
            have hR : ‖r‖ ≤ ‖x‖ := by simpa [K] using h
            rw [eH]; exact (hb r (hR.trans hX)).trans (by gcongr)
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le (s:=K) (f:=u) (fun x _=>hd x) HK (convex_closedBall ..) (x:=0) (y:=x)
      (by simp [K] : (0:Mom) ∈ K) (by simp [K])
    change ‖u x‖ ≤ _
    rw [show u x=u x- u 0 from by unfold u; rw [jets_zero hz (by omega : j≤M),sub_zero]]
    simpa [pow_succ,mul_assoc] using he
lemma jets_bound (M : ℕ) (f : Probe Mom) (hz : FlatAns M 0 f) (N j : ℕ) (h:j+N≤M) : ∃ C≥(0:ℝ), ∀ x:Mom, ‖x‖≤1→ jj j f x ≤ C*‖x‖^N := by
    induction N generalizing j with
    | zero => exact ⟨_,apply_nonneg ..,fun x _=>by simpa using jj_le j f x⟩
    | succ k IH => exact jj_highBound f j k M (by omega) hz (IH (j+1) (by omega))

end YM.Trace.Shell
