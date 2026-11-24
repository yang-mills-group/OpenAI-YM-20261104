import YM.Pert.Phases.Funds

/-! Uniformity *over* characters for fixed correcting probes (not over arbitrary geometries). -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Pert.PhaseControl
open Function Filter Topology Set MeasureTheory Analysis Extraction Retain Table Maxwell Cells Bid Org OS
open scoped BigOperators Classical Topology
variable {G:Gauge} {C:Family G} {F:Order} {S:Table C.book} (B:Spec.Final C F S)
variable {d:ℕ} {X:Columns C S d} (Y:X.Trials) (Q:Y.Valid F)

lemma any_phase (s:ℕ→members B) (i c) (hf:Funds Y Q B.α.unselected) :
      Tendsto (fun k=>observed B Y k (s k) i c) atTop (𝓝 ((X.row i).tests (standard C) X.basis (X.basis c))) := by
   let U k:= observed B Y k (s k) i c
   let T k:= (standard C).useAt (standard C) (Y.tested k i) (testFns (X:=X) i c)
   let a:=(X.row i).tests (standard C) X.basis (X.basis c)
   have ht : Tendsto T atTop (𝓝 a) := limits Y Q i c
   suffices H : Tendsto (fun k=> U k - T k) atTop (𝓝 0) by
       have hh:= (H.add ht).congr fun k=>show _=(U k) from sub_add_cancel ..; simpa only [zero_add] using hh
   by_cases hx : (X.row i).extra = 0
   · exact squeeze_zero_norm (fun k=>show ‖U k-T k‖ ≤ Y.gap k from lowCharge B Y Q s _ _ hf k hx) Y.small
   have h:(X.row i).extra = 1:=Nat.le_antisymm (X.row i).cap (Nat.pos_of_ne_zero hx)
   let t : Fin ((X.row i).extra+1) := ⟨1,by omega⟩
   let R t' k:=‖Y.singleton k i c t'‖
   obtain ⟨x₁,h₁⟩:=singletonGone Y Q i c 0
   obtain ⟨x₂,h₂⟩:=singletonGone Y Q i c t
   have hy:= h₁.norm.add h₂.norm
   have hd : Tendsto (fun k=>Y.gap k+(R 0 k+R t k)*Y.gap k) atTop (𝓝 0) := by simpa only [mul_zero,zero_add] using Y.small.add (hy.mul Y.small)
   exact squeeze_zero_norm (fun k=> highCharge B Y Q s i c hf k t (show 0 < t from Nat.zero_lt_one)) hd

/-- Real basis columns in `Cols` source reference coordinates. -/
def phaseField (k : ℕ) (s:members B) : (standard C).Field d→L[ℂ](phase B s).Field d :=
    (X.basis.constr ℂ (fun i=>(phase B s).project d (Y.later k i))).toContinuousLinearMap

def instruments (k : ℕ) (s:members B) : (standard C).Field d →L[ℂ] (Fin X.amount → ℂ):=
    ((LinearMap.pi (probe' (D:=phase B s) Y k)).comp (phaseField B Y k s).toLinearMap).toContinuousLinearMap

def freeBoard : (standard C).Field d →L[ℂ] (Fin X.amount → ℂ) :=
    let test (i : Fin X.amount) : (standard C).Field d→ₗ[ℂ] ℂ := Ward.here (q := Fin.cons ⟨d,(0:(standard C).Field d)⟩ (fun s => ⟨d,X.basis ((X.row i).uses s)⟩)) (X.row i).expected 0 d
    (LinearMap.pi test).toContinuousLinearMap

lemma instruments_sample (i c k s) : instruments B Y k s (X.basis c) i = observed B Y k s i c := by
   change (probe' (D:=phase B s) Y k i ((X.basis.constr ℂ _ : _ →ₗ[ℂ] _ ) (X.basis c))) = _
   simp only [Module.Basis.constr_basis]; rfl

lemma freeBoard_sample (i x) : freeBoard (X:=X) x i = (X.row i).tests (standard C) X.basis x := by
   change ((Ward.here (q := Fin.cons ⟨d,(0:(standard C).Field d)⟩ (fun s => ⟨d,X.basis ((X.row i).uses s)⟩)) (X.row i).expected 0 d) x) = _
   rw [Ward.takes]
   unfold SampleRow.tests Ward.disc
   congr 1
   ext1 s; refine Fin.cases ?_ (fun l=> ?_) s <;> simp

variable (hf:Funds Y Q B.α.unselected)
include hf
lemma board_late (v:ℕ→members B) :
   Tendsto (fun k=>instruments B Y k (v k)) atTop (𝓝 (freeBoard (X:=X))) := by
   let a k:=instruments B Y k (v k)
   let b:=freeBoard (X:=X)
   have ht(c:Fin _) : Tendsto (fun k=> a k (X.basis c)) atTop (𝓝 (b (X.basis c))) := by
       apply tendsto_pi_nhds.mpr; intro i
       change Tendsto (fun k=> instruments _ _ k _ _ i) atTop (𝓝 (freeBoard _ i))
       simp_rw [instruments_sample,freeBoard_sample]; exact any_phase B Y Q v i c hf
   let F' := (standard C).Field d
   let E : Type:= Fin X.amount → ℂ
   let H:=X.basis
   let M : ((Fin (X.dim+1))→E) →ₗ[ℂ] F' →L[ℂ] E := {
       toFun p := LinearMap.toContinuousLinearMap (H.constr ℂ p)
       map_add' p q := by change LinearMap.toContinuousLinearMap (H.constr ℂ (p+q))=_; rw [map_add (H.constr ..), map_add]
       map_smul' c p := by change LinearMap.toContinuousLinearMap (H.constr ℂ (c • p))=_; rw [map_smul (H.constr ..), map_smul];rfl }
   have hb (g:F' →L[ℂ] E) : M (fun i=> g (H i))=g := by
      apply ContinuousLinearMap.coe_injective
      exact H.ext (fun i => H.constr_basis ..)
   let y := (fun x i=> (a x) (H i))
   have hl:= M.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (show ∀ c, Tendsto (Function.eval c ∘ y) atTop (𝓝 (b (H c))) from ht))
   have hl' : Tendsto (fun x=>a x) atTop (𝓝 b):= by
      have ht:=hl.congr (fun i=>hb _)
      rwa [hb] at ht
   exact hl'

lemma board_uniform {ε:ℝ}(hε:0 < ε) :
   ∀ᶠ k:ℕ in atTop,∀ v, ‖instruments B Y k v-freeBoard (X:=X)‖ ≤ ε := by
    letI : Nonempty (members B) := ⟨B.α.atPoint⟩
    let s k:= Classical.epsilon (fun v=> ‖instruments B Y k v-freeBoard (X:=X)‖ > ε)
    let E := (standard C).Field d
    let P i := ((X.basis.coord i).toContinuousLinearMap : E →L[ℂ]ℂ)
    let c:= ∑ i:Fin (X.dim+1), ‖P i‖
    let δ:= ε/(c+1)
    have h0:0 ≤ c:= Finset.sum_nonneg fun i hi=> (P i).opNorm_nonneg
    have hd : δ ≥ 0 := (div_nonneg hε.le (by linarith only [h0]))
    let A (k:ℕ):= instruments B Y k (s k)
    let T:=freeBoard (X:=X)
    have H:∀ i j,∀ᶠ k in atTop, ‖(A k-T) (X.basis i) j‖ ≤ δ := by
       intro i j
       have ht := any_phase B Y Q s j i hf
       have he : Tendsto (fun k=>A k (X.basis i) j) atTop (𝓝 (T (X.basis i) j)) := by simpa only [A,T,instruments_sample,freeBoard_sample] using ht
       exact (Metric.tendsto_nhds.1 he δ (div_pos (by linarith) (by linarith))).mono fun k hk=> by
          rw [dist_eq_norm] at hk
          exact hk.le
    filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (H i))] with k hk
    have hA i : ‖(A k-T) (X.basis i)‖ ≤ δ:= pi_norm_le_iff_of_nonneg hd |>.2 (by convert! hk i)
    have he (x:E) : ‖(A k-T) x‖ ≤ ε*‖x‖ := by
        have hv : (A k-T) x= ∑ i:Fin (X.dim+1), (P i x) • ((A k-T) (X.basis i)) := by
           conv_lhs=> rw [←X.basis.sum_repr x,map_sum]
           simp_rw [map_smul]; rfl
        rw [hv]
        apply (norm_sum_le ..).trans
        simp_rw [norm_smul]
        calc
          _ ≤ ∑ i:Fin (X.dim+1), ‖P i‖ * (δ*‖x‖) := Finset.sum_le_sum fun i hi=> by
                simpa only [← mul_assoc, mul_comm δ] using mul_le_mul ((P i).le_opNorm x) (hA i) (norm_nonneg _) (by positivity)
          _ = c*(δ*‖x‖) := by rw [←Finset.sum_mul]
          _ ≤ _:= by
             rw [←mul_assoc]
             apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
             dsimp only [δ]; rw [mul_div_assoc',div_le_iff₀ (by linarith only [h0])]; nlinarith only [hε.le]
    intro v
    by_contra! hv
    have hp : ε < ‖A k-T‖:= Classical.epsilon_spec (show ∃ v, ‖instruments B Y k v-freeBoard (X:=X)‖ > ε from ⟨v,hv⟩)
    exact hp.not_ge ((A k-T).opNorm_le_bound hε.le he)

end YM.Pert.PhaseControl
