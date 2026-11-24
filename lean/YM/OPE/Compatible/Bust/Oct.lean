import YM.OPE.Compatible.Bust.Earth
/-!
# Extract from variable periods in a grade. At Bed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra RG Work.F08 Matrix
open scoped Topology BigOperators Classical
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ}{N c:Side}{v:Train r}{G:Gauge} {L:KernelChoices}
lemma coupled (i:ℕ)(p:Seat k m (Shade G)) (u:Site N)(y:Fin i→ deck (Shade G) N): formSong m k G u p i (fun j=>(deckW G N).symm (y j))=scribe u (lilies m k _ p i) y :=by
     rw [tensors]; congr! 1; ext1 j; exact (deckW G N).apply_symm_apply _
-- phase value recovery OWN shift for Lamp : pass to multiples.
private def adaptM (h:c.val∣N.val)(p:deck I c): deck I N:=fun i=>p (trimT N c h i.1,i.2)
lemma stintM {f:Filter X}(q:X→ Seat k m (Shade G))(p:Seat k m (Shade G))(hq:Tendsto q f (𝓝 p))(n:X→Side)(h:∀ i,c.val∣(n i).val)(u: Fin r→deck (Shade G) c): Tendsto (fun i=> scribe (0:Site (n i)) (lilies m k _ (q i) r) (fun j=> adaptM (h i) (u j))) f (𝓝 (scribe 0 (lilies m k _ p r) u)) :=by
     let F(Q:Seat k m (Shade G)):=reading m r (0:Site c) (moduleAt m k r _ Q); have he(Q): scribe 0 (lilies m k _ Q r) (u) = F Q u:= (instruments _ (tiller _ (moduleAt m k r _ Q)) ..).tsum_eq.trans (by unfold F; rw [toScript])
     have hA(i): scribe (0:Site (n i)) (lilies m k _ (q i) r) (fun j=> adaptM (h i) (u j))=F (q i) u:=by
          rw [← he]; unfold scribe; refine tsum_congr fun j=>congr_arg (lilies m k _ (q i) r j* ·) ?_
          unfold render; refine prod_congr rfl fun a _=>?_ ; unfold adaptM; dsimp only; rw [_root_.map_add,lease,map_zero]
     simp_rw [hA,he]; exact ((show Continuous (fun x=> F x u) from Continuous.comp (ContinuousMultilinearMap.apply ℝ _ _ u).continuous ((reading m r 0 ∘L moduleAt m k r (Shade G)).continuous)).tendsto p).comp hq
lemma phiV (x:deck G.ColorIndex c): Prog L v G c *ᵥ ((deckW G c).symm (cliff x))=0:=by
     let u:Vec G c 0:=fun i=>x (i.1,i.2.2); rw [show (deckW G c).symm (cliff x)=gradient u from (by rw [← (show deckW G c (gradient u)=cliff x from slopeCliff u), LinearEquiv.symm_apply_apply]),raster]
lemma cloakM (h:c.val∣N.val)(x:deck G.ColorIndex c):adaptM h (cliff x)=cliff (adaptM h x):=by ext1 i; unfold cliff adaptM; rw [map_add,← wrap_step (n:=N), lease,wrap_step] -- API
lemma scopeX (v:Train r)(h:4 ≤ r){p:Seat k (m+1) (Shade G)}(hp:p∈ bed G k (m+1)): lapD (atlasF G v h L) (m+1) k p∈bed G k (m+1):=by
     let y:= lapD (atlasF G v h L) (m+1) k p; intro j; let P:= lilies (m+1) k (Shade G); have ht:∀ n:Side, ∀ x:Fin j→ deck (Shade G) n,
           (∀ a:Equiv.Perm (Fin j),scribe 0 (P y j) (x ∘ a)=scribe 0 (P y j) x) ∧ (∀ i:Fin j, ∀ v:deck G.ColorIndex n, scribe (0:Site n) (P y j) (update x i (cliff v))=0)∧ (∀ u:G.El,scribe (0:Site n) (P y j) (fun i=> hue u (x i))=scribe (0:Site n) (P y j) x) := by
              intro n x; let τ(i:ℕ):Side:=⟨n.val*(i+1),mul_pos n.pos (Nat.succ_pos _)⟩ -- m clash
              let g(i):= lapD (pointAt G v h L (τ i)) (m+1) k p; have hm(i):n.val∣(τ i).val:= dvd_mul_right ..; have hh:Tendsto (fun i=>(τ i).val) atTop atTop:=tendsto_atTop_mono (fun i=> (show i≤ i+1 from Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ n.pos)) tendsto_id
              have he(u:Fin j→ deck (Shade G) n):= stintM g y ((loreLap (m:=m+1) (farN G τ v h L hh)).p2 p) τ hm u -- k
              let ℓ(t:ℕ)(x:deck (Shade G) n):=adaptM (hm t) x; let T(t):= formSong (m+1) k G (0:Site (τ t)); let R(t:ℕ)(v):Vec G (τ t) 1:= (deckW G _).symm (ℓ t v); have hpA(u: Fin j→deck (Shade G) n)(t:ℕ): scribe 0 (P (g t) j) (fun i=>ℓ t (u i))=T t (g t) j (R t ∘ u):=(coupled j (g t) _ (fun i=>ℓ t (u i))).symm
              have hz(i):= sax (N:=τ i) (L:=L) hp v h j 0
              refine ⟨fun a=>tendsto_nhds_unique_of_eventuallyEq (he _) (he _) ?_,fun i v'=>tendsto_nhds_unique_of_eventuallyEq (he _) tendsto_const_nhds ?_,fun u=>tendsto_nhds_unique_of_eventuallyEq (he _) (he _) ?_⟩
              · filter_upwards with i; exact (hpA (x∘ a) i).trans (( (hz i).1 (R i ∘ x) a).trans (hpA x i).symm)
              · filter_upwards with l; let U:=R l ∘ update x i (cliff v'); let V:= (deckW G _).symm (cliff (adaptM (hm l) v')); have he:U i=V:=by unfold U V R ℓ; rw [Function.comp_apply,update_self,cloakM]
                refine (hpA _ l).trans ?_; change T l (g l) j U=0; rw [← (show update U i V=U from he ▸ update_eq_self ..)]; exact (show T l (g l) j (update U i V)=0 from (hz l).2 _ _ _ (phiV _))
              filter_upwards with l; let z(i):= R l (hue u (x i)); let Y:= (magicL G (τ l) u); have hQ(i): Y*ᵥ(R l (x i))=z i:=by rw [magicB]; unfold z R chipHue; rw [LinearEquiv.apply_symm_apply];rfl
              apply (hpA (fun j=>hue u (x j)) l).trans; change T l (g l) j z=_; have ht: T l (g l) j (fun i=> Y*ᵥ (R l ∘ x) i)=T l (g l) j (R l∘ x):= DFunLike.congr_fun (repel (L:=L) hp u v h j (τ l)) (R l ∘ x); rw [show z=(fun i=>Y*ᵥ(R l∘x) i) from funext fun i=> (hQ i).symm]; exact ht.trans (hpA x l).symm
     let q:= P y j; have hp: soot (m+1) q ‖y‖:= (sproutV _ _ y).2 j; have hh:= sootS hp; refine ⟨⟨_,hp⟩,fun i n w p=> (ht n w).2.1 ..,fun n w u=>(ht n w).2.2 u,fun a=>?_⟩
     ext1 i; refine tendsto_nhds_unique_of_eventuallyEq (lands (swing a q) (swing_sum q hh a) i epochX (l:=atTop) (tendsto_add_atTop_nat 1)) (lands q hh i epochX (tendsto_add_atTop_nat 1)) ?_; filter_upwards with j; exact (rotating ..).trans ((ht (epochX j) (hand i (epochX j))).1 a)
end YM.OPE.Silt.Float
