import YM.FormalOPE.RG10.Position.Fresh

/-! # Enforcing single field-space projections with one TestSystem tower
(not the interactions/denominator comparison). -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Physical.Profile PertExtension.Physical PertExtension.Position
  PowerSeries
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {F : Frames G} {d k n : ℕ}

-- name clashes
section general
variable {P J K : Type*} (shape:P→ℕ) [Fintype J] [Fintype K]

def ascend (j:J→K) (v:Mark J shape): Mark K shape:=⟨v.1,j ∘ v.2⟩
variable (j:J→K)

def clip {R:Type*} (A:FrameAt K R):FrameAt J R:=fun i k=> A (j i) (j k)

def lowers {R:Type*} [Zero R] (A : FrameAt K R) := ∀ i : J,∀ x∉Set.range j, A (j i) x=0

lemma promote {R:Type*}[CommSemiring R](A: FrameAt K R)(p : Mark K shape → R) (v : Mark J shape) (hj:Injective j) (hA : lowers j A) :
    PertExtension.Position.insert K shape p A (ascend shape j v)= PertExtension.Position.insert J shape (p ∘ ascend shape j) (clip j A) v:= by
  unfold PertExtension.Position.insert
  let J' := Fin (shape v.1); let f(x:J'→J): J'→K := j ∘ x
  let F(w:J'→K) := p ⟨v.1,w⟩ * ∏ i,A (j (v.2 i)) (w i)
  have hf: Injective f:= fun _ _ h=>funext fun i=>hj (congr_fun h i)
  change ∑ s:J'→K, F s=∑ t:J'→J,F (f t)
  conv_rhs => rw [← Finset.sum_image (f:=F) (by exact hf.injOn)]
  symm; refine Finset.sum_subset (subset_univ _) ?_
  intro i _ hi; have he:∃ k,i k∉Set.range j:=by
    by_contra! ht; choose x hx using ht; exact hi (mem_image.mpr ⟨x,mem_univ _,funext hx⟩)
  obtain ⟨k,hk⟩:=he; unfold F; rw [Finset.prod_eq_zero (mem_univ k) (hA _ (i k) hk),mul_zero]

-- freely reusable test restriction condition. use with compatible unit and H variations on Deck.
variable (D:TestSystem J P shape)(E:TestSystem K P shape)
structure Bindings : Prop where
  base : D.baseline = clip j E.baseline
  varies : ∀ u∈E.Z, clip j u ∈D.Z
  bottom : lowers j E.baseline
  left : ∀ u∈E.Z, lowers j u
  tags (r : Mark K shape→ℝ) : clip j (E.select (r ∘ markIn E.tests)).val=(D.select (r ∘ ascend shape j ∘ markIn D.tests)).val
  targets : clip j E.target.val=D.target.val

variable {j D E shape}
namespace Bindings
variable (h : Bindings shape j D E) (u:E.Z)
include h
def project : E.Z →ₗ[ℝ] D.Z where
  toFun u := ⟨_,h.varies _ u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _:= rfl
lemma bounding : lowers j (E.baseline + u.val):= fun i k hk=>by simp only [Pi.add_apply,h.bottom _ _ hk,h.left _ u.property _ _ hk,add_zero]
lemma works (a : Mark K shape →ℝ) (hj:Injective j) : h.project (E.lieResult (a ∘ markIn _) u)= D.lieResult ((a ∘ ascend shape j) ∘ markIn _) (h.project u) := by
  apply Subtype.ext; unfold TestSystem.lieResult
  rw [TestSystem.result_eq, TestSystem.result_eq]
  change clip j _= _
  rw [h.tags]
  have he : clip j (E.baseline+u.val)=D.baseline+(h.project u).val := by rw [h.base]; rfl
  rw [← he]; refine congr_arg Subtype.val (congr_arg D.select ?_); funext x;
  exact promote shape j _ _ _ hj (h.bounding u)

-- coherence after shift selection at free point. baseline now projects all Solve. `mk` ℝ ok.
lemma atCenter (b : Mark K shape→ℝ⟦X⟧) : lowers j (E.position b) := by
  intro i x hx; ext n : 1; cases n with
  | zero=> simpa using h.bottom i x hx -- coeffs baseline
  | succ n=> rw [map_zero]; exact h.left _ (TestSystem.positive_variation E b (n+1) (by omega)) i x hx

lemma cast (hj:Injective j) {a : Mark K shape→ℝ⟦X⟧} (hd:D.Regular (fun v=>constantCoeff (a (ascend shape j v)))) (he:E.Regular (fun i=>constantCoeff (a i))) : D.position (a ∘ ascend shape j) = clip j (E.position a) := by
  let b:= a ∘ ascend shape j
  change D.position b= _
  apply D.uniqueness (a:=b) hd
  · intro n; apply Subtype.ext
    have hQ:= TestSystem.normalizes D hd n (a:=b)
    have ht:= congr_arg (fun u:E.Z=> clip j u.val) (TestSystem.normalizes E he n); unfold TestSystem.response at ht
    have hZ:= h.tags (fun v=> coeff n (PertExtension.Position.insert K shape a (E.position a) v)) -- tc
    -- will reduce comp
    rw [hQ]
    dsimp only [comp_apply, Function.comp_def] at hZ; simp_rw [promote shape _ _ _ _ hj (h.atCenter a)] at hZ
    unfold TestSystem.response
    rw [← hZ, ht]; split <;> rename_i H
    · exact h.targets.symm
    rfl
  · simp
  · intro i k; rw [h.base]; unfold clip; simp
  intro n hn
  apply D.Z.sub_mem (x:=clip j (fun i k=>coeff n (E.position a i k))) (y:=fun i k=>coeff n (D.position b i k)) (h.varies _ (E.positive_variation ..)) (D.positive_variation ..)<;> omega

-- Avoid possible ambiguity between branch construction via constant solve and post positioning
-- via implicit solve on a supplied free tower. Prove (eventual) exact alignment.
variable (a : Mark K shape→ℝ) (p:ℕ→ Mark K shape→ℝ)
local notation "z" => ascend shape j
local notation "a'" => a ∘ (ascend shape j)
local notation "g" m => p m ∘ (ascend shape j)
omit h in
private lemma pair_rank (D:TestSystem J P shape)(p: Mark J shape→ℝ) (hp:D.Regular p) : Function.Bijective (fderiv ℝ D.solver (p∘ markIn D.tests,(0:D.Z))) := (D.eventually_fullrank p hp).self_of_nhds

lemma shifting (hj:Injective j) (hd:D.Regular a')(he:E.Regular a)
    (hv:∀ x,Tendsto (fun m=>p m x) atTop (𝓝 (a x))) :
    ∀ᶠ m in atTop,D.branch a' ((g m) ∘ markIn _) = h.project (E.branch a (p m ∘ markIn _)) := by
   let P m:= (g m) ∘ markIn D.tests; let Q:= a' ∘ markIn D.tests; let U:=(Q,(0:D.Z));
   let P' m:= p m ∘ markIn E.tests;
   let Q' := a ∘ markIn E.tests;
   have hm : Tendsto P atTop (𝓝 Q):=tendsto_pi_nhds.mpr (fun _=> hv ..)
   have hm': Tendsto P' atTop (𝓝 Q'):=tendsto_pi_nhds.mpr (fun _=> hv ..)
   have hP:= (D.tends a' hd).comp hm
   have hP':= (E.tends a he).comp hm'; let t:= fun m=>h.project (E.branch a (P' m));
   have hs:Tendsto t atTop (𝓝 (0:D.Z)):= (show (0:D.Z)=h.project 0 from (map_zero ..).symm) ▸ (h.project.continuous_of_finiteDimensional.continuousAt.tendsto.comp hP'.snd_nhds)
   let L:=fderiv ℝ D.solver U; let B:=(LinearEquiv.ofBijective L.toLinearMap (pair_rank D a' hd)).toContinuousLinearEquiv -- coercions inspect
   have hh:HasStrictFDerivAt D.solver (B.toContinuousLinearMap) U:= D.smooth_solve.hasStrictFDerivAt (by simp)
   filter_upwards [hm.eventually (D.solves a' hd), hm'.eventually (E.solves a he), (hm.prodMk_nhds hs).eventually (HasStrictFDerivAt.eventually_left_inverse (f':=B) hh), hP.eventually (HasStrictFDerivAt.eventually_left_inverse (f':=B) hh)] with i ha hb hc hh'
   have ht : D.solver ((P i),(D.branch a' (P i)))=D.solver (P i,t i) := by
     unfold TestSystem.solver; change (P i,D.lieResult (P i) _)=(_,D.lieResult (P i) _); rw [ha]; unfold P t; rw [← h.works _ _ hj,hb]; exact congr_arg _ ((Subtype.ext h.targets).symm : D.target=h.project E.target)
   apply congr_arg Prod.snd (hh'.symm.trans ((congr_arg _ ht).trans hc))

include h
lemma rebind (hj:Injective j) (hd:D.Regular a')(he:E.Regular a)
    (hv:∀ x,Tendsto (fun m=>p m x) atTop (𝓝 (a x))) : ∀ᶠ m in atTop,
    Bindings shape j (D.leadingAdjust a' (g m)) (E.leadingAdjust a (p m)) := by
  filter_upwards [h.shifting a p hj hd he hv] with i hi
  refine ⟨?_,h.varies,h.bounding _,h.left,h.tags,h.targets⟩
  show D.baseline+_=clip j (E.baseline+_)
  rw [h.base,hi]; rfl
end Bindings
end general
end YM.FormalOPE.RG10.Position
