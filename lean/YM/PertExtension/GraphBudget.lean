import Mathlib
/-! Compact bound transfer on moving mesh points. Covers with an approximate
point for each configuration are important in applying an all-indices path
convergence to sparse tests. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.PertExtension.GraphBudget
open Function Set Filter Metric
open scoped Topology Classical
variable {X:Type*}[TopologicalSpace X]{V:ℕ→Type*}{S:∀ n,V n→X}{G:∀ n,V n→ℝ}{K:Set X}

lemma extend_strict {φ:ℕ→ℕ}(hφ:StrictMono φ)(v:∀ n:ℕ,V (φ n)) {x:X}
    (h:Tendsto (fun n=> S (φ n) (v n)) atTop (𝓝 x))(h₂:∃ w: ∀ n,V n,Tendsto (fun n=> S n (w n)) atTop (𝓝 x)): ∃ u:∀ n,V n, (∀ n,u (φ n)=v n)∧Tendsto (fun n=>S n (u n)) atTop (𝓝 x):=by
  obtain ⟨w,h₂⟩:=h₂
  let pred(n):= ∃ j,φ j=n
  let u (n:ℕ):V n:= if h:pred n then (Classical.choose_spec h) ▸ v (Classical.choose h) else w n
  have he n : u (φ n)=v n:=by
    have ht:pred (φ n) :=⟨n,rfl⟩
    have hz := hφ.injective (show φ (Classical.choose ht) = φ n from Classical.choose_spec ht)
    unfold u;rw [dif_pos ht]; generalize_proofs hp hg
    have hE : HEq (v (Classical.choose ht)) (v n):= dcongr_heq (heq_of_eq hz) (fun i j (h:HEq i j) => by subst_vars; rfl) (fun _ _=>HEq.rfl)
    exact (eqRec_heq _ _ |>.trans hE).eq
  refine ⟨u,he, fun U hU=>?_⟩
  obtain ⟨n,hn⟩:= eventually_atTop.mp (h hU); obtain ⟨m,hm⟩:=eventually_atTop.mp (h₂ hU)
  change ∀ᶠ a:ℕ in atTop,S a (u a)∈U
  filter_upwards [eventually_ge_atTop (max (φ n) m)] with a ha
  by_cases ha':pred a
  · obtain ⟨j,rfl⟩:=ha'
    rw [he j];exact hn j (hφ.le_iff_le.mp (le_trans (le_max_left ..) ha)) -- he orientation
  rw [show u a=w a from dif_neg ha']; exact hm _ (le_trans (le_max_right ..) ha)

variable [FirstCountableTopology X]
lemma wallet (hK:IsCompact K){T:X→ℝ}
    (h0:∀ x∈K,∃ u:(i:ℕ)→V i,Tendsto (fun i=>S i (u i)) atTop (𝓝 x))
    (h:∀ (u:(i:ℕ)→V i) x,x∈K → Tendsto (fun i=>S i (u i)) atTop (𝓝 x) → Tendsto (fun i=>G i (u i)) atTop (𝓝 (T x))):∃ b≥0,∀ᶠ n:ℕ in atTop,∀ v:V n,S n v∈K→‖G n v‖≤b:=by
   classical
   by_contra! hneg
   have H(m:ℕ):∃ n:ℕ,m<n ∧ ∃ v:V n,S n v∈K ∧ (m:ℝ)<‖G n v‖:= by
      obtain ⟨n,⟨v,hv,hV⟩,hp⟩:=((hneg (↑m:ℝ) (by positivity)).and_eventually (eventually_gt_atTop m)).exists
      exact ⟨_,hp,v,hv,hV⟩
   choose f₀ hf v₀ hv hn using H -- v₀ m at f₀ m
   let p :ℕ→ℕ:=Nat.rec 0 (fun _ v=>f₀ v)
   have hp m : m≤p m:=by induction m with | zero=>rfl | succ m h=> exact h.trans_lt (hf _)
   let f:= f₀ ∘ p; let v m:V (f m):=v₀ (p m)
   have hs : StrictMono f:= strictMono_nat_of_lt_succ (fun n=>(hf (f n):f n<p (n+2))) -- wrong
   have ht (i): S (f i) (v i)∈K∧(i:ℝ)<‖G (f i) (v i)‖:=⟨hv _,(Nat.cast_le.mpr (hp i)).trans_lt (hn _)⟩
   obtain ⟨x,hx,φ,hp,hP⟩:= hK.isSeqCompact (x:=fun i=> S (f i) (v i)) (fun i=> (ht i).1)
   obtain ⟨u,Hu,HB⟩:= extend_strict (hs.comp hp) (fun i=> v (φ i)) (x:=x) hP (h0 x hx)
   have hy : Tendsto (fun i=>(φ i:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp hp.tendsto_atTop
   have hm: Tendsto (fun i=>‖G (f (φ i)) (u (f (φ i)))‖) atTop (𝓝 ‖T x‖) := ((h u x hx HB).comp (hs.comp hp).tendsto_atTop).norm
   obtain ⟨i,hi,hv⟩:= ((show ∀ᶠ i in atTop,‖G (f (φ i)) (u (f (φ i)))‖≤‖T x‖+1 from hm.eventually (ge_mem_nhds (by simp))).and (hy.eventually_ge_atTop (‖T x‖+1))).exists
   have h':u (f (φ i)) = v (φ i):= Hu i
   exact (not_lt_of_ge (hi.trans hv)) (by rw [h'];exact (ht _).2)
end YM.PertExtension.GraphBudget
