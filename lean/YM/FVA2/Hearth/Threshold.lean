import YM.FVA2.Facade.Gluing
/-!
 # The true whole group, prefix gap on its interior truss.
 ONLY at fixed period (inversion), for comparing formal coefficient calculations;
 this isn't estimating the real hierarchy.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade
open scoped Classical Topology BigOperators ContDiff
variable {G: Gauge} {c f n:Side} {L:Fabric G n} (T:Cloth L)
private lemma fully {n:Side}{L: Fabric G n}(T: Cloth L)(x: Warm T→G.El){i} (h:T.choose.Branch i) : rear L 1 (door T x) i=1:= by
 cases T with
 | floor=> cases i with
           | inl i=> rfl
           | inr i=> exact Empty.elim i
 | @inLayer c f S H t hf L P C=>
    let T0:= Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
    cases i with
    | inl i=> exact door_tree T0 x _ ((sprig_now P (fir C) i).mpr ((P.inner_only H t hf C.choose i).mp h))
    | inr i=>
       let x'(a):= x (Sum.inr a)
       let j:L.Path:= i
       have he:(fun k:Used L=> door T0 x (Sum.inr k))=door C x':= funext fun k=> enlisted k x
       change rear L 1 (fun k:Used L=> door T0 x (Sum.inr k)) j=1; rw [he]; exact fully C x' ((P.outer_only H t hf C.choose j).mp h)
termination_by structural T
private lemma rear_scalar {n:Side}(L: Fabric G n){x:Used L→ G.El} (h:rear L 1 x=1): x=1:= by
 cases L with
 | endcap=> exact funext fun i=> Empty.elim i
 | @layer c f S H t hf L=>
    funext i; change OEdge _⊕ Used L at i; cases i with
    | inl i=> exact congr_fun h (Sum.inl i)
    | inr i=> exact congr_fun (rear_scalar L (funext fun u=> congr_fun h (Sum.inr u))) i
termination_by structural L
private lemma full (x:Warm T→G.El) : T.choose.bulk (rear L 1 (door T x))=1 → x=1:= by
 intro hx; have ht:T.choose.board 1=rear L 1 (door T x):= by rw [←hx,T.choose.board_bulk,T.choose.already _ (fun _ h=> fully _ _ h)];
 have he:= rear_scalar L (ht.symm.trans T.choose.board_one); funext i
 let a:= (leeway T) i; rw [← Equiv.symm_apply_apply (leeway T) i,← door_loop T x ((leeway T) i)]; exact congr_fun he a.val

variable (y:Flats G (Bottom L))
local notation "X"=> (Warm T→ G.El)
@[fun_prop] lemma committed_cont : Continuous (Function.uncurry (committed T y)):= by
 refine (rear_cont L).comp (Continuous.prodMk ?_ ((door_cont T).comp continuous_snd))
 exact continuous_pi (fun i=>(G.lieExp_cont.comp ((continuous_fst.smul (g:=fun _:ℝ×X=>y i) continuous_const)))) -- notation binding

lemma gap (S:Set X)(hs:IsOpen S) (hw:1∈ S) : ∃ K ∈ 𝓝 (1:T.choose.Bulk → G.El), ∀ᶠ g:ℝ in 𝓝 0,∀ x ∉ S, T.choose.bulk (committed T y g x) ∉ K:= by
 let P:= fun v:ℝ×X=> T.choose.bulk (Function.uncurry (committed T y) v); have hp : Continuous P:= T.choose.bulk_cont.comp (committed_cont T y)
 let H := Sᶜ; have hH: IsCompact H:= hs.isClosed_compl.isCompact
 let V:= fun x:X=>P (0,x)
 have h0 : (1:T.choose.Bulk→G.El)∉ V '' H:= by
  rintro ⟨x,hx,h⟩; apply hx; suffices p : x=1 from p.symm ▸ hw
  apply full T; dsimp only [V,P,Function.uncurry_apply_pair,committed] at h; rwa [zero_smul,Inherit.identity_zero] at h
 obtain ⟨A,B,ha,hb,hV,hb₀,hd⟩:= IsCompact.separation_of_notMem (x:=(1:T.choose.Bulk→G.El)) (hH.image (hp.comp (continuous_const.prodMk continuous_id)) : IsCompact (V '' H)) h0
 refine ⟨B,hb.mem_nhds hb₀, hH.eventually_forall_of_forall_eventually (P:=fun g x=> T.choose.bulk (committed T y g x)∉ B) (fun x hx=> (hp.tendsto (0,x)).eventually ((ha.mem_nhds (hV ⟨x,hx,rfl⟩))) |>.mono (fun w hw => Set.disjoint_left.mp hd hw))⟩

variable (w:L.Accounts→ℝ→ℝ)(hu:∀ i,ContinuousAt (w i) 0)(hp:∀ i,0< w i 0)
include hu hp
lemma uniformFront (S:Set X)(hs:IsOpen S)(hw:1∈ S): ∃ c>0, ∀ᶠ r : ℝ in 𝓝 0,∀ x∉ S,c ≤ front T w y r x:= by
 let p (i):= w i 0/2
 obtain ⟨K,hK,hk⟩:= gap T y S hs hw
 obtain ⟨c,hc,h⟩:= (Inherit.prepared L T.choose p (fun i=> half_pos (hp i))).cut K hK
 have hu':∀ᶠ r in 𝓝 (0:ℝ), ∀ i,p i≤ w i r:= eventually_all.mpr fun i=> ((hu i).eventually (eventually_ge_nhds (half_lt_self (hp i))))  -- p
 refine ⟨c,hc,?_⟩; filter_upwards [hk,hu'] with r hr hb; intro x hx; apply le_trans (b:=L.spend p (committed T y r x)) _ (Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hb _) (L.price_nonneg ..))); by_contra! hh
 let a:= committed T y r x
 apply hr x hx (h _ (show L.spend p (T.choose.board (T.choose.bulk a))<c from ?_)); rw [T.choose.board_bulk,Loom.Truss.treeGauge,L.invariant_cost]; exact hh
end YM.FVA2.Hearth
