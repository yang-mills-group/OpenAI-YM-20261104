import YM.FormalBulk08.Aster.Lender

/-! Pledge handles reader cost before L. Any number predecessor inputs
already strict and allotted. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Lattice Laurent Bloch Exterior RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X:Type}{E e r m s n u:ℕ}
-- local law
structure Pledge (G:Gauge)(K:KernelChoices)(F:Flight n u)(V:Lodge F.patch)(σ η A Q δ R:ℝ)(m:ℕ):Prop where
   shop : ∀ W:Tile (edgeL G) (m+1), Up W → Agate W → Valed W →∀ B Y:ℝ,Bail (fame _) σ W B→ Bail (fame _) σ (tap W) Y →
      ∃ C:ℝ,Bail (fame _) η (risePath F V G K W) C ∧ (1+A*Q)*C ≤ δ*B+R*Y
lemma promises (G:Gauge)(K:KernelChoices){σ η A Q C:ℝ} (h:0<σ)(e:0<η)(hp:0≤A)(ht:0≤Q)(hc:0≤C)(hm:1≤m): ∃ B:ℝ,0<B∧∀ (P:Patch) (T:Lodge P)(U:ℝ),0≤U →∃ D:ℝ,0<D∧∀ (F:Flight n u) (V:Lodge F.patch), ∀ p:F.patch=P, p ▸ V=T→ Threshold σ η m F.L → η ≤ F.L.val * σ → (locating G K F V).strip η U → (roots G K F V).strip η U → gauss (Flight.duo K.penalty F).A0 η C (4-m) →∀ δ:ℝ, B/(F.L.val:ℝ) ≤ δ → Pledge G K F V σ η A Q δ D m:=by
   obtain ⟨X,hX,H⟩:= anchor_quote (j:=n) (t:=u) G K h e hc hm; let R:=1+A*Q;have hR:0<R:=by unfold R; positivity
   refine ⟨R*X,mul_pos hR hX,fun P T U hu=>?_⟩; obtain ⟨D,d,W⟩:=H P T U hu; refine ⟨R*D,mul_pos hR d,fun F V ho ha he hK hP hU hG δ hx=>?_⟩
   refine ⟨fun T ht hb hz B Y hB hY=> ⟨_, W _ _ ho ha he hK hP hU hG _ hb ht hz _ _ hB hY, ?_⟩⟩
   change R* _ ≤ _; calc
       _ = (R*X/(F.L.val:ℝ))*B + R*D*Y:= by ring
       _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right hx hB.1) _
structure Angler (G:Gauge)(η C:ℝ)(e n:ℕ):Prop where
    plus : 0<C
    value : ∀ T:Pot G, Authorized T → Agate (T e (n+1)) → Up (T e (n+1)) → ∀ B, 0≤B → (∀ j<e,∀ i,1 ≤ i→ i≤n+1 → Bail (fame _) η (T j i) B) → Bail (fame _) η (tap (T e (n+1))) (C*B)
lemma anglers (G:Gauge)(σ:ℝ)(h:0≤σ)(e m:ℕ):∃ C:ℝ,Angler G σ C e m:= by obtain ⟨C,c,H⟩:= revenue G e m h; exact ⟨C,c,H⟩
variable {τ:Time X} {σ η δ A B C D:X→ℝ} {T U:X→Pot G}
lemma purse_here {T:X→ Pot G}(hA:Soft τ C)(ht:∀ i,Angler G (σ i) (C i) e n)(ha:∀ i,Authorized (T i))(hp:∀ i, Agate (T i e (n+1)))(he:∀ i,Up (T i e (n+1)))(hr:∀ j<e,∀ k,1≤k→ k≤ n+1→ Cost τ (fun _=>fame _) σ (fun i=> T i j k)): Cost τ (fun _=> fame _) σ (fun i=>tap (T i e (n+1))) := by
    let F:=Finset.range e ×ˢ Finset.Ico 1 (n+2)
    obtain ⟨B,u,p,Q⟩:= cost_pay F (fun i hi=> hr i.1 (Finset.mem_range.mp (Finset.mem_product.mp hi).1) i.2 (Finset.mem_Ico.mp (Finset.mem_product.mp hi).2).1 (Nat.le_of_lt_succ (Finset.mem_Ico.mp (Finset.mem_product.mp hi).2).2))
    refine ⟨_,hA.times u,fun i=> (ht i).value _ (ha i) (hp i) (he i) _ (p i) (fun j h l u e=> Q (j,l) (by unfold F;simp [h,u,e,Nat.lt_succ_iff]) i)⟩
lemma dusty_here (h0:∀ x,0≤δ x)(hA:Soft τ C)(ht:∀ i,Angler G (σ i) (C i) e n)(ha:∀ i, Authorized (T i))(hp:∀ i, Agate (T i e (n+1)))(he:∀ i,Up (T i e (n+1)))(hr:∀ j<e,∀ k,1≤ k→k≤n+1→ Dust τ (fun _=>fame _) σ δ (fun i=> T i j k)): Dust τ (fun _=>fame _) σ δ (fun i=>tap (T i e (n+1))) := by
    let F:=Finset.range e ×ˢ Finset.Ico 1 (n+2)
    obtain ⟨B,b,H,Q⟩:= dust_pay F h0 (fun i hi=>hr i.1 (Finset.mem_range.mp (Finset.mem_product.mp hi).1) i.2 (Finset.mem_Ico.mp (Finset.mem_product.mp hi).2).1 (Nat.le_of_lt_succ (Finset.mem_Ico.mp (Finset.mem_product.mp hi).2).2))
    refine ⟨_,hA.times b,fun i=> mul_nonneg (ht i).plus.le (H i),fun i=>?_⟩;rw [mul_assoc]; exact (ht i).value _ (ha i) (hp i) (he i) _ (mul_nonneg (H i) (h0 i)) (fun j hj l u e=> Q (j,l) (by unfold F;simp [hj,u,e,Nat.lt_succ_iff]) i)
lemma frame_valence {T:Pot G}{R:Row (TypeFace 2) (TypeFace 2)}(h:FrameV T R)(e:0<r): Valed (T r m):= by intro i;subst m; exact h.seals r e
lemma valed_sub {T U:Pot G}{R S: Row (TypeFace 2) (TypeFace 2)}(h:FrameV T R)(ht:FrameV U S)(he:0<e)(a:hue G)(hs:G.Simple): Valed ((T-U) e n):= by
    intro i;subst n;change Cork.Null (T e 2-U e 2); apply direct_nil (splendid_sub (splendid h.toStory _) (splendid ht.toStory _)) hs a; exact (value_less (h.fare e _) (ht.fare e _) a).trans (by rw [show value a _=0 from (h.seals e he).water 1 1 a a 0 0, show value a _=0 from (ht.seals e he).water 1 1 a a 0 0,sub_zero])
-- simplify predecessors; requirement j=0 even optional if r big

def floor_cost (τ:Time X)(σ:X→ℝ)(T:X→Pot G)(e n:ℕ):Prop:= ∀ j m,1≤m→m≤ j+2→ precede e n j m→ Cost τ (fun _=> fame _) σ (fun i=>T i j m)
def floor_dust (τ:Time X)(σ δ:X→ℝ)(T U:X→Pot G)(e n:ℕ):Prop:=∀ j m,1≤m→m≤ j+2→precede e n j m→ Totem τ (fun _=> fame _) σ δ (fun i=>T i j m) (fun i=>U i j m)
lemma floorCost_lower (h:floor_cost τ σ T e r)(ht:∀ i,Vivid (T i))(k m)(hr:1≤m)(hx:precede e r k m): Cost τ (fun _=>fame _) σ (fun i=> T i k m) := by
    by_cases he:m≤ k+2; exact h k m hr he hx
    simp_rw [show ∀ i,T i k m=0 from fun i=>by by_contra hp; exact he ((ht i).valence _ _ hp).2.1]; apply cost_void
lemma floorDust_lower (h:floor_dust τ σ δ T U e r)(ht:∀ i,Vivid (T i))(hp:∀ i,Vivid (U i))(k m)(hr:1≤m)(hx:precede e r k m): Totem τ (fun _=> fame _) σ δ (fun i=> T i k m) (fun i=> U i k m) := by
    by_cases he:m≤k+2;exact h k m hr he hx
    simp_rw [show ∀ i,T i k m=0 from fun i=>by by_contra h; exact he ((ht i).valence _ _ h).2.1,show ∀ i,U i k m=0 from fun i=>by by_contra h; exact he ((hp i).valence _ _ h).2.1];apply voids
end YM.FormalBulk08.Aster
