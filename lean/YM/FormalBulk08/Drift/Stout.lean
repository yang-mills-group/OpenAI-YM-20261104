import YM.FormalBulk08.Drift.Vega
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Drift
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {I:Type}{G:Gauge}{η C:ℝ}{σ:ℕ→ℝ}{K:KernelChoices}{E e r d D n R:ℕ}{ρ:ChartRatio G}{o: Loc G 1}
-- Rite through, explicitly not Rite outside paid degree. independent matrix algebra
-- reads can handle unsupported higher orders, no Ward given.
def Sonority (Y X: Anthem D G)(l:ℕ)(s:Signed)(E:ℕ):Prop:=∀ n p (I:Type)[Fintype I](a b : Jets.Rays I→Jets.Rays (wire G n))(k: Jets.Rays I → Site n→G.El), a 0=0 → b 0=0 → ContDiffAt ℝ ω a 0 → ContDiffAt ℝ ω b 0 → Army k 0 → (∃ g:G.El,k 0=fun _=>g) → (∀ᶠ z in 𝓝 0,input G n (b z)=Lattice.gauge (k z) (pull s 0 (input G n (a z)))) → Through E (roam ℝ (motor a) (Kemp.banner l (Y p) n)) (roam ℝ (motor b) (Kemp.banner l (X (froth s D p)) n))
lemma parrot {s:Signed}{T S:ℕ→ Anthem D G}{P Q:Anthem D G}{z:Loc G 1} (l:ℕ)(h:∀ i,Son (T i) (S i) l s)(hp:∀ e≤ E,∀ r,Brass staticT o (fun _=>η) σ (fun _=>1) (fun i p=>T i p e r) (fun _ p=>P p e r))(hx:∀ e≤ E,∀ r,Brass staticT z (fun _=>η) σ (fun _=>1) (fun i p=> S i p e r) (fun _ p=>Q p e r))(he:0≤η)(hv:Ends σ 0)(hh:∀ i,0≤σ i): Sonority P Q l s E:= by
    intro n p I i a b k hA hB ha hb hc hk he' m hm; ext1 d
    let U (i: Side) := Kemp.banner l (T i.val p) n; let V(i:Side) := Kemp.banner l (S i.val (froth s D p)) n
    have hf:= marble_copy l n hp he hv hh; have hg:= marble_copy l n hx he hv hh
    have hU:=moors U (Kemp.banner l (P p) n) (motor a) (fun j=>l+j) (fun j hj=> .of_forall (fun n=>(hf j hj).2 p n.val)) (fun j hj i v=> ((hf j hj).1 p i v).comp highlim) _ hm d
    have hV:= moors V (Kemp.banner l (Q (Dawn.froth s D p)) n) (motor b) (fun j=>l+j) (fun j hj=>.of_forall (fun n=>(hg j hj).2 (froth s D p) n.val)) (fun j hj i v=>((hg j hj).1 (froth s D p) i v).comp highlim) _ hm d
    have ht i : roam ℝ (motor a) (U i) = roam ℝ (motor b) (V i):= h i.val n p I a b k hA hB ha hb hc hk he'
    simp_rw [ht] at hU; exact tendsto_nhds_unique hU hV
lemma orbit_match [Fintype I] {J:Type} {T S:ℕ→ I→ Anthem D G}{Q W:ℕ→ Matrix I J Pence} (j:J)(h:∀ e≤ E,∀ r x,Brass staticT o (fun _=>η) σ (fun _=>1) (fun i p=>T i x p e r) (fun i p=> S i x p e r))(hp:∀ i, Priced staticT σ (fun z=>Q z i j) (fun z=> W z i j) E) (he:e≤E): Brass staticT o (fun _=>η) σ (fun _=>1) (fun i p=> larch (T i) (Q i) j p e r) (fun i p=>larch (S i) (W i) j p e r):= by
    unfold Brass larch; simp only [Kemp.launch,surf,Finset.sum_apply]; apply matched_sums _; intro i _; apply matched_sums _; intro p hp'; rw [Finset.mem_antidiagonal] at hp'; have ht : p.1 ≤ E := by omega
    have hv : p.2 ≤ E:=by omega
    exact Matched.amp (h p.2 hv _ i) (hp i _ ht)

variable {X: Type}{W:Lab G K X}{F:Frame G d}{H:Hol G}{T:SectionData F}
-- trunk above cut has no coefficients outside, rights only through.
def sliceM (T:Anthem D G)(E:ℕ): Anthem D G:= fun p=> stopper (T p) E
variable (q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤R)(he:e≤ E)(i:Letter F)(x:Leaf W.scrolls)
include h u q a hs ht hb hr
lemma rations_limit : Wade o (sliceM (issue W ρ a F T q.horizon x.a x.b i) E) (slots F i) ∧ IsLinearMap ℝ (sliceM (issue W ρ a F T q.horizon x.a x.b i) E):= by
   let g j:= bornY ρ W a F T q.horizon x.a (j+x.b) x.b i; let Y:= issue W ρ a F T q.horizon x.a x.b i; let W':= sliceM Y E; let l:= Pose.slots F i; have hp j: Clef o (g j) l:= (birth a h q hs ht hb _ _ _ x.zone (show x.b≤j+x.b by omega)).officers i
   have he (e r)(h:e≤ E)(p:Studio D)(v): Ends (fun j=> g j p e r v) (W' p e r v):= by
       have hT : W' p e=Y p e:= if_pos h; rw [hT]; exact (tendsto_add_atTop_iff_nat x.b).mpr ((Drift.harbor q u ‹LocalRatio ρ› a hs ht hb hr h i r x p).shares v)
   have hz p j (h:E < j) r: W' p j r=0:= by unfold W' sliceM stopper; rw [if_neg (not_le.mpr h)];rfl
   change Wade o W' _ ∧ IsLinearMap ℝ W'
   refine ⟨⟨fun p e r hz'=>?_,fun p e r=>?_,fun e r=>?_⟩,⟨fun p r=>?_,fun c p=>?_⟩⟩
   · by_contra hh; apply hz'; by_cases ht:e≤ E
     · funext v; refine tendsto_nhds_unique (he e r ht p v) (tendsto_const_nhds.congr' (.of_forall fun i=>?_));exact (congr_fun (show g i p e r=0 from Classical.byContradiction fun hv=>hh ((hp i).fare.1 p e r hv)) v).symm
     exact hz _ _ (by omega) _
   · by_cases ht:e≤E
     · exact fun x s=> tendsto_nhds_unique (he e r ht p (x ∘ s)) ((he e r ht p x).congr' (.of_forall fun i=> ((hp i).fare.2.1 p e r x s).symm))
     rw [hz _ _ (by omega)]; apply agate_zero
   · by_cases Hk:e≤ E;swap
     · simp_rw [hz _ _ (show E<e from lt_of_not_ge Hk)]; refine ⟨1,0,one_pos,le_rfl,fun _=>by rw [zero_mul];exact Knox_zeros _⟩
     obtain ⟨C,c,k,H⟩:= skiff q u h a hs ht hb hr Hk i r; exact ⟨_,_,u.zero x,k x,fun p=>by rw [show W' p e=Y p e from if_pos Hk]; exact (H x p).1⟩
   · funext e n v; by_cases H:e≤ E;swap
     · simp_rw [Pi.add_apply,hz _ _ (lt_of_not_ge H),Pi.zero_apply,add_zero]
     exact tendsto_nhds_unique (he e n H (p+r) v) (((he e n H p v).add (he e n H r v)).congr' (.of_forall fun i=>by dsimp only; rw [(hp i).map_add]; rfl))
   funext i n v; by_cases h:i≤E; swap
   · simp_rw [Pi.smul_apply,hz _ _ (lt_of_not_ge h),Pi.zero_apply,smul_zero]
   exact tendsto_nhds_unique (he i n h _ v) (((he i n h p v).const_mul c).congr' (.of_forall fun i=>by dsimp only; rw [(hp i).map_smul];rfl))
lemma rotor (s:Signed): Sonority (larch (issue W ρ a F T q.horizon x.a x.b) (lariat F s) i) (issue W ρ a F T q.horizon x.a x.b i) d s E := by
   let Y N:= bornY ρ W a F T q.horizon x.a (N+x.b) x.b;let t(n):=fare_n x (n+x.b); have hv k:Harmonized F s (Y k):=Elm.harmony a h q hs ht hb _ _ _ x.zone (by omega) s
   have hz j:= hv j i; have hp e (he:e≤E) r j:= pantry_prices q u h a hs ht hb hr he j r x
   exact parrot (σ:= t) _ hz (fun e he r=> orbit_match (Q:=fun _=>lariat F s) (T:=Y) i hp (fun j=> Priced.constant _ _ (lariat F s j i) _) he) (fun e he r=>hp e he _ i) (u.zero x).le ((tendsto_add_atTop_iff_nat x.b).mpr (fare_fin x)) (fun i=> (ratioR_pos ..).le)
lemma single_convention : Sonority (issue W ρ a F T q.horizon x.a x.b i) (issue W ρ a F T q.horizon x.a x.b i) (slots F i) 1 E:= by
    have he j: Court o F (bornY ρ W a F T q.horizon x.a (j+x.b) x.b):= birth a h q hs ht hb _ _ _ x.zone (by omega)
    exact parrot (slots F i) (fun j=>((he j).officers i).ward) (fun e hv r=> pantry_prices q u h a hs ht hb hr hv i r x) (fun e hv r=>pantry_prices q u h a hs ht hb hr hv i r x) (u.zero x).le ((tendsto_add_atTop_iff_nat _).mpr (fare_fin x)) (fun _=>(ratioR_pos ..).le)
end YM.FormalBulk08.Drift
