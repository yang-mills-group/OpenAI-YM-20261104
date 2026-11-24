import YM.Contacts.Shuttle.Broker
/-! # Transport on finite periods. Exact Ward moment on whole charge, preserves beyond plain rank-zero -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace YM.Contacts.Shuttle.Tide
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Broadcast
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{m:ℕ→Side}{F:Cohort G}{h k u n :ℕ}
namespace Morning
local notation "N"=> Node (Dyes G)
lemma full (a : Draft G h) : a∈ Jar G h (h+1):= ⟨Powers.widen _ _ (Nat.le_succ _) (spot a.1),fun i hi=>by omega⟩
lemma waterJet (H:Hol G) (hm:Tendsto (fun j=>(m j).val) atTop atTop)(hk:k*(h+1) ≤ u)(v:Fin k→ Draft G h)(x:N): ∀ᶠ j in atTop,
    iteratedFDeriv ℝ k (north H (m j)) 0 v (lower (m j) x) = Tide.lens G u x (iteratedFDeriv ℝ k (rain G h u) 0 v):= by
   rcases x with ⟨x,a,z⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective a
   filter_upwards [eventually_all.mpr fun j : Fin k=> unfolds_wood (v j) hm x a] with i hi; change iteratedFDeriv ℝ k (north H (m i)) 0 v (wrap (m i) x,coord a,z)=Tide.lens _ _ (x,coord a,z) _
   rw [north_turn, glaze_at, derivative_glow v _ _ (fun _=> h+1) (fun i=>⟨by omega, full (v i)⟩) (by simp only [sum_const,card_univ,Fintype.card_fin, smul_eq_mul]; omega), derivative_shine, show timber (m i) (wrap (m i) x) a ∘ v=_ from (show _=fun j=> sight (xyz x) a (glow G.Color _ (v j).1) (v j).2 from funext fun j => hi j)]
open FormalMultilinearSeries OrderedFinpartition
private def upworld (p:OrderedFinpartition k){E:Type}(T: Draft G h → E) [NormedAddCommGroup E][NormedSpace ℝ E] (v:Fin k→Draft G h) (j:Fin p.length) := iteratedFDeriv ℝ (p.partSize j) T 0 (v ∘ p.emb j) -- § req NormedSpace E
private lemma settle_axis {P:∀ i, Link G (m i)→ℝ} (H:Hol G)(hm:Tendsto (fun j=>(m j).val) atTop atTop)(hf:Felt F)(p:OrderedFinpartition k)(v:Fin k → Draft G h) (hk:k*(h+1)≤u)(hu:k≤n)(ht:∀ j,Ticket (P j) F n) :
    Tendsto (fun j=> iteratedFDeriv ℝ p.length (P j) 0 (upworld p (north H (m j)) v)) atTop (𝓝 (iteratedFDeriv ℝ p.length (rows F u n) 0 (upworld p (rain G h u) v))) := by
   let T:=p.length; let y:= ∑ i:Fin T, p.partSize i; let M i (j:Fin T):= upworld p (north H (m i)) v j; let U:=upworld p (rain G h u) v; let W i (j:Fin T) (x:N):ℝ:=M i j (lower (m i) x); have hi : p.length ≤ n:=p.length_le.trans hu
   have hs : Tendsto (fun i=> say (F T) (W i)) atTop (𝓝 (say (F T) (fun j x=> lens G u x (U j)))):= by
      choose b hb hB using fun j:Fin T=> needs (p.partSize j) (v∘p.emb j) H; obtain ⟨x,s,hs,B,hx⟩:= hf.alone T
      refine settling hx hs (Finset.sum_nonneg (s:=univ) fun i _=>hb i) (n:=k*h) (Eventually.of_forall fun i j x'=>?_ ) (fun i j=> EventuallyEq.tendsto (waterJet H hm (Nat.le_trans (by gcongr; exact partSize_le ..) hk) (v∘p.emb i) j))
      exact (hB j (m i) x').trans (mul_le_mul (single_le_sum (fun i _=> hb i) (mem_univ j)) (pow_le_pow_right₀ (show 1 ≤ blast x' by unfold blast; simp) (Nat.mul_le_mul_right h (p.partSize_le j))) (by unfold blast; positivity) (sum_nonneg fun i _=> hb i))
   let β (i:ℕ):= Tensor.coeff (P i) p.length 0 (M i); let V:= Tensor.coeff (rows F u n) p.length 0 U
   have hh:Tendsto β atTop (𝓝 V):= by unfold β V; rw [hf.plans u hi, sheet_read (hf.board T u)]; exact hs.congr (fun i=> ((ht i).points_tensor hf hi _).symm)
   have hs : (p.length.factorial:ℝ) ≠ 0:= by positivity
   have he(X:Type)(I:NormedAddCommGroup X)(K:NormedSpace ℝ X)(f:X→ℝ)(v:Fin T→X):iteratedFDeriv ℝ T f 0 v= (p.length.factorial:ℝ)*Tensor.coeff f T 0 v:= by change _=(p.length.factorial:ℝ)*((p.length.factorial:ℝ)⁻¹*_); rw [mul_inv_cancel_left₀ hs _]; rfl
   conv=>arg 1; ext j; rw [he (Link G (m j)) inferInstance inferInstance]
   rw [he (Ship G u) inferInstance inferInstance]; exact hh.const_mul _
lemma settlement {P:∀ i, Link G (m i)→ℝ} (H:Hol G)(hm:Tendsto (fun j=>(m j).val) atTop atTop)(hf:Felt F) (v:Fin k→Draft G h) (hk:k*(h+1)≤u)(hu:k≤n)(ht:∀ j,Tide.Ticket (P j) F n) :
   Tendsto (fun j=> iteratedFDeriv ℝ k ((P j) ∘ north H (m j)) 0 v) atTop (𝓝 (iteratedFDeriv ℝ k (rows F u n ∘ rain G h u) 0 v)) := by
   have he j: ContDiffAt ℝ ω (P j) (north H (m j) (0: Draft G h)):= by rw [north_zero]; exact (ht j).clear.contDiffAt
   have hz : ContDiffAt ℝ ω (rows F u n) (rain G h u 0):= rows_diff F u n|>.contDiffAt
   simp_rw [iteratedFDeriv_comp (he _) (north_diff (G:=G) _ H h) (show (k:WithTop ℕ∞) ≤ ω from le_top), north_zero,iteratedFDeriv_comp hz (germ_rain G h u) (show (k:WithTop ℕ∞) ≤ ω from le_top), rain_base,FormalMultilinearSeries.taylorComp, _root_.sum_apply]; exact tendsto_finsetSum _ fun i _=> settle_axis (P:=P) H hm hf i v hk hu ht
end Morning
end YM.Contacts.Shuttle.Tide
