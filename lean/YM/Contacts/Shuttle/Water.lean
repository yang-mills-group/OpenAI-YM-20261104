import YM.Contacts.Shuttle.Stunt
/-!
# Precision collar for marked momentum

On the whole gauge-invariant charge, *not* horizontally truncated at a given coupling order.
Serves both the norm gain and the returned projection. Later Tries must assemble Tickets on proper orbit arithmetic/speaker compacts.
-/
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace YM.Contacts.Shuttle.Tide.Morning
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Broadcast Mom WardBin -- Merging?
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{m:Side}{F:Cohort G}{h d k u n :ℕ}
-- retain h, n demanded on charge (often h) and interpolate standard radius u
abbrev room (F:Cohort G)(d u n:ℕ): Draft G d→ℝ:= rows F u n ∘ rain G d u
abbrev plank (G:Gauge)(d:ℕ): Snap G d→L[ℝ] Draft G d:= ContinuousLinearMap.inr ℝ _ _
abbrev fresh (G:Gauge)(d:ℕ): Draft G d→L[ℝ] Snap G d:= ContinuousLinearMap.snd ℝ _ _
abbrev panel (F:Cohort G)(d u n:ℕ): Snap G d→ℝ:= room F d u n ∘ plank G d
lemma native (H:Hol G){f:Config G m→ℝ}(hf:GaugeInvariant f): (fun a: Draft G d=> f (input G m (north H m a))) =ᶠ[𝓝 0] (fun a=> f (frameAt H m a)):= by
    have he: Tendsto (raft (h:=d) H m) (𝓝 0) (𝓝 1):= by rw [← raft_base m H d]; exact (raft_port m H d).cont
    filter_upwards [he.eventually content_encodes] with i hi; unfold north; rw [hi,raft,hf]
private lemma risk0 (F:Cohort G)(d u n:ℕ): ContDiffAt ℝ ω (room F d u n) 0:= (rows_diff F u n).contDiffAt.comp _ (germ_rain ..)
lemma smooth_panel (F:Cohort G)(d u n:ℕ): ContDiffAt ℝ ω (panel F d u n) 0:= ContDiffAt.comp (f:=⇑(plank G d)) _ (g:=room F d u n) (by rw [(plank G d).map_zero]; exact risk0 ..) (plank G d).contDiff.contDiffAt
lemma steadies (hf:Tags F) (H:Hol G)(d u:ℕ)(hk:k*(d+1) ≤ u)(hn:k≤n)(v:Fin k→ Draft G d):
   iteratedFDeriv ℝ k (room F d u n) 0 v= iteratedFDeriv ℝ k (room F d u n) 0 (fun i=> plank G d (fresh G d (v i))):= by
   let L(i:ℕ):Side:=⟨i+1,by omega⟩; have he:Tendsto (fun i=>(L i).val) atTop atTop:= StrictMono.tendsto_atTop (show StrictMono fun i=> (L i).val from strictMono_nat_of_lt_succ fun i=>(by change i+1 < i+1+1; omega)); choose f Hf Hg hT using fun i=> hf.oath (L i) n; let P i:=f i ∘ input G (L i); let U:= (plank G d).comp (fresh G d); have hv (w:Fin k→ Draft G d):= settlement (P:=P) H he hf.toFelt w hk hn hT
   apply tendsto_nhds_unique (hv v); let χ (j:ℕ):=P j ∘ north (h:=d) H (L j); apply (hv (fun i=> U (v i))).congr; intro i; let Q:= frameAt (h:=d) H (L i); have hh:χ i=ᶠ[𝓝 0] f i ∘ Q:= native H (Hg i); have ht: Tendsto U (𝓝 0) (𝓝 0):= by simpa using U.continuous.tendsto 0
   have hy : χ i ∘ U =ᶠ[𝓝 0] χ i:= (hh.comp_tendsto ht).trans hh.symm
   have hc : ContDiffAt ℝ ω (χ i) 0:= by unfold χ; refine ContDiffAt.comp _ ?_ (north_diff _ H d); rw [north_zero]; exact (hT i).clear.contDiffAt
   exact ((DFunLike.congr_fun (Next.Foundations.jets_linear (k:=k) U (hc.of_le le_top)) v).symm.trans (DFunLike.congr_fun (hy.iteratedFDeriv ℝ k|>.eq_of_nhds) v))
lemma erased (hf:Tags F) (H:Hol G)(d u:ℕ)(hk:k*(d+1)≤u)(hn:k≤n)(v:Fin k→ Draft G d):
   iteratedFDeriv ℝ k (room F d u n) 0 v= iteratedFDeriv ℝ k (panel F d u n) 0 (fresh G d ∘ v):= by rw [steadies hf H d u hk hn]; exact (DFunLike.congr_fun (Next.Foundations.jets_linear (k:=k) (plank G d) ((risk0 F d u n).of_le le_top)) (fresh G d ∘ v)).symm
def unreads (F:Cohort G)(d u n h:ℕ):Prop:= Weighted.evolved (fun i:Fin (d-1)=> i.val+2) (Mom.deck (G:=G)) h (panel F d u n)
open Mediator
lemma baltic (hf:Tags F)(ha:h≤d)(hb:d≤n)(hc:d*(d+1)≤u)(hy:unreads F d u n h): valence (fun i=>(Jar G d i:Set _)) h (room F d u n) := by
    obtain ⟨H⟩ := Hol.exists_ode G -- check namespace
    intro k a v he; have hv1 : ∀ i,1 ≤ a i:= fun i=> (he.1 i).1; have hk: k≤d:= by have hx:= Finset.sum_le_sum (f:=fun i=>1) (s:=univ) (fun i _=> hv1 i); simp at hx; exact (hx.trans he.2).trans ha
    rw [erased hf H d u (le_trans (Nat.mul_le_mul_right _ hk) hc) (hk.trans hb)]; apply Weighted.cancel (fun i : Fin (d-1) => i.val+2) (deck (G:=G)) _ (fun i => by omega) decks hy ((smooth_panel ..).of_le le_top) _ a hv1 he.2; intro i x hx; rw [deck_at]; change Pi.single x ((v i).2 x)= (0:Snap G d); rw [((he.1 i).2 : v i∈Jar G d (a i)).2 x hx, Pi.single_zero]
def sail (F:Cohort G)(d u n:ℕ)(S:ℕ) : Prop:= valence (Draws G u) S (rows F u n)
theorem motion (hf:Tags F)(ha:h≤d)(hb:d≤n)(hc:d*(d+1)≤u)(hy:unreads F d u n h): sail F d u n h:= by
    have hU: d≤u:= (show d ≤ d*(d+1) from le_mul_of_one_le_right (by omega) (by omega)).trans hc
    refine attenuation _ _ (rain G d u) (rows F u n) ((germ_rain ..).of_le le_top) (rain_base ..) ((rows_diff F u n).contDiffAt.of_le le_top) (fun i hi h v hv=> rain_surj hU hi (h.trans ha) v hv) ?_ (baltic hf ha hb hc hy)
    intro m hm a v he; exact rain_health hU m hm a v ⟨he.1, he.2.trans ha⟩
local notation "NV"=> Node (Dyes G)
def Polynomials (G:Gauge)(k:ℕ)(b : Fin k→ℕ)(v:Fin k → Node (Dyes G) → ℝ) :=∀ i, ∃ f : Axis → E4 → G.Color,(∀ a,f a∈ Powers.space E4 G.Color (b i-1))∧ ∀ z a l,v i (z,coord a,l)= (f a (xyz z)) l
lemma moment_null (hf:Tags F)(ha:h≤d)(hb:d≤n)(hc:d*(d+1)≤u)(hy:unreads F d u n h)(b:Fin k→ℕ)(v:Fin k → NV → ℝ)(ht:Polynomials G k b v)(hB:∀ i,1≤ b i)(hq:∑ i,b i≤h): say (F k) v=0 := by
    have hU: d≤u:= (show d ≤ d*(d+1) from le_mul_of_one_le_right (by omega) (by omega)).trans hc; have hk:k ≤ d:= by have hx:= Finset.sum_le_sum (f:=fun i=>1) (s:=univ) (fun i _=> hB i); simp at hx; exact (hx.trans hq).trans ha
    choose g H hz using ht; let V(i: Fin k): Ship G u:= fun a=>fit u (g i a); have he i: V i ∈ Draws G u (b i):= fun a=>⟨_,H i a,rfl⟩; have hM:= motion hf ha hb hc hy k b V ⟨fun i=>⟨hB _,he _⟩,hq⟩
    have HH : Tensor.coeff (rows F u n) k 0 V=0:= by unfold Tensor.coeff; simp [hM] -- impute
    rw [hf.plans u (hk.trans hb), sheet_read (hf.board ..)] at HH; suffices hw:v=(fun i x=> lens G u x (V i)) by rw [hw]; exact HH
    funext i ⟨z,a,y⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective a; change v i (z,Exterior.coord a,y)= Tide.lens G u (z,Exterior.coord a,y) (V i); rw [hz i z a,glaze_at]; unfold V; rw [sky (Powers.widen _ _ ((Nat.sub_le (b i) 1).trans ((single_le_sum (f:=b) (fun i _=> Nat.zero_le _) (mem_univ i)).trans ((hq.trans ha).trans hU))) (H i a))]
end YM.Contacts.Shuttle.Tide.Morning
