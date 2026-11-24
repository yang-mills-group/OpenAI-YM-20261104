import YM.FormalBulk08.Tundra.Won
import YM.FormalBulk08.Avenue.Junction

/-! Cutoff GDP for D and first step emissions. Captured stock may be subject to
just these polynomial bounds. Require model-phase as defined on same horizon.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover Dove Castor North Spruce Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X I:Type}{E m l e r u D R d:ℕ}{o:Loc G 1}{W:Lab G K X}{F:Frame G d}{T:SectionData F}{H:Hol G}{ρ:ChartRatio G}
variable {g δ:X→ℝ}{τ:Time X}{Y Z:X→Anthem D G}{θ:ℝ}

open Avenue Trellis Grail Dove.Lab Orb Wick Series Jets
lemma whee (B:X→ℝ)(Q:X→edgeL G→edgeL G→ℝ)(h:Soft τ B)(hp:∀ i,0≤B i)(hb:∀ i x y,‖Q i x y‖≤ B i){T:X→Studio D→Tile (edgeL G) (r+2)}(ht:Sigh u τ o g T) : Sigh u τ o g (fun i p=>stare (Q i) (T i p)):= by
    obtain ⟨C,c,v,H⟩:=ht; let n:ℝ:=1/2*(r+2)*(r+1); refine ⟨_,(soft_coin τ n).times (h.times c),fun i=>mul_nonneg (by unfold n; positivity) (mul_nonneg (hp _) (v _)),fun i p=>?_⟩; convert knox_stare (H i p) (Nat.cast_nonneg u) (hb i) (hp i) using 1;unfold n;ring
lemma pageants (B:X→ℝ)(Q:X→edgeL G→edgeL G→ℝ)(h:Soft τ B)(hp:∀ i,0≤B i)(hb:∀ i x y,‖Q i x y‖≤ B i){T:X→Studio D→Beams (edgeL G)}(ht:∀ r,Sigh u τ o g (fun i p=>T i p r))(l :ℕ): Sigh u τ o g (fun i p=> pageant (Q i) (T i p) l r):= by
    unfold Sigh pageant; apply bear_sums _; intro i _; suffices H:∀ n j,Sigh u τ o g (fun i p=>bleat (Q i) (T i p) n j) from Bear.amp (H i r) (soft_coin τ _)
    intro n; induction n with
    | zero=> exact ht
    | succ n ih=> exact fun j=> whee B Q h hp hb (ih _)
variable (q:Quota F H W o D E R) (h:Use W ρ E)(p:Nesting F D E R u W o)(c: Extras W)(a:hue G)(v: LocalRatio ρ)(hs:G.Simple)(ht:T.Sound H)(hb: Bid.pop T)(hR:d≤ R)(hl:l≤ R)(hr:θ<1/2)(hr':0≤θ)(C P:Pin W.scrolls)(hc:∀ i,C.N i≤ P.N i) (hp: Erudit τ W.scrolls C)(hx:∀ i,Clef o (Y i) l)(hz:∀ i,0≤g i)(hw:∀ e≤E,∀ r,Wayfarer Y e r u ((sage C).reach (peak C)) o g)
include h q a v hs ht hb hc hx
lemma calm_yes (i: Deck C): Clef o (calmTop l T ρ Y q a C P i) l:= by
   have ht':= classifier q h v a hs ht hb C P hc hx i;exact ht'.1.sub (larch_cleared _ _ (frozen_winged q h v a hs ht hb C P hc hx i) ((birth a v q hs ht hb _ _ _ i.zone (i.cap.trans (hc i.a))).officers) ())
include hp hR hl c hr hr' p hw hz
lemma Winside (x:Letter F):
    let Q:=fun i:Deck C=> coastEye C P l i F (calmTop l T ρ Y q a C P i)
    Faint (rday τ C) (fun i=>g i.a*Degree θ (startP i.a C)) (fun i=> Q i x):= by
    intro q'; let f i:= g i*Degree θ (startP i C);
    have ht' (i:Turn C):= (mat_begins a v q hs ht hb i.a i.b (P.N i.a) i.zone (i.head.trans_le (hc i.a))).1; let U(i:Turn C):= noncontract F (echoR T ρ q a C P i)
    let Q'(i:Turn C):= echoR T ρ q a C P i; let b(i: Turn C)(x):=heightK ((W.V i.a).S.block i.b) d (Pose.weight F x)
    have ha i: Found (slots F) (Pose.weight F) (tag (U i)) (b i):= nc_stamp (Q' i) _ (ht' i); have hb'(i:Turn C) j:1≤ b i j:= crown_weight ..
    let A i:= calmTop l T ρ Y q a C P i
    have hA i:=calm_yes q h a v hs ht hb C P hc hx i
    have hf i:0≤f i:=mul_nonneg (hz i) (ratioR_pos ..).le
    have hJ:=tabular hp.origin hp.depth h.liable
    refine faint_forward (Q:=q') (b:=fun i j=>(b i j)⁻¹) (T:=fun i=>(U i)⁻¹) (w:=Pose.weight F) (s:=Pose.slots F) (fun i=>?_ ) (?_) (?_) (?_) (fun i j=> inv_le_one_of_one_le₀ (hb' i j)) hf (raySteps hp.depth) _
    rotate_left
    · intro i; rw [(tagBack (ha i)).2]; exact primes (ha i)
    · intro y
      let s:=fun i=> startP i C;let g i:= calmTop l T ρ Y q a C P (s i); let N(k:X):=P.N k; let R' i:=location (W.V i) (N i) (W.neck i); let B i:= mediumP G K ((W.V i).clock.J (W.neck i)); let A' i:= bandP G (R' i) K.penalty; let η i:= W.windowD (s i).toLeaf
      have he i: Fees G K ((W.V i).clock.J _) (B i):= fee_live G K _ ((W.V i).clock.adm _)
      have hp':Soft τ B:= town_fold (g:=fun i:X=>(s i).toLeaf) hp.origin c
      have hw' e r (hx':e≤E) : Sigh u τ o f (fun i p=>g i p e r) := lynx s (soft_day τ) (Matched.left (harvested q p h v a hs ht hb C P P hc (fun _=>le_rfl) hl hR hz hx hx (fun j hj k=> Matched.constant (hw j hj k)) hp hr hr' hx' r))
      have hT t : Sigh u τ o f (fun i p=>winner (R' i) K.penalty l (g i) p t):=pageants B A' hp' (fun i=>(he i).active) (fun i j k=>(he i).cords _ _ _) (T:=fun i p=>g i p 0) (fun r=> hw' 0 r (Nat.zero_le E)) l
      change Faint τ f (fun i=> pearlJ F (winner (R' i) K.penalty l (g i) (inside F y D) (slots F y)) (mint F y))
      exact Tundra.tilted (T:=fun i z=>winner (R' i) K.penalty l (g i) z (Pose.slots F y)) y (hT (slots F y)) p.plus
    · have hc(i j:Letter F): Soft (qday τ C) (fun x=> coeff 0 (Q' x i j)) := by
         let g (x:Turn C):transferPoint W:=⟨x.toLeaf,P.N x.a,P.N x.a,x.head.trans_le (hc x.a),le_rfl⟩; exact town_fold (g:=g) (hJ.reach (fun i:Turn C=>i.bed)) ((staccato q h v hs ht hb a hR i j 0 (Nat.zero_le E)).left)
      exact nc_invoice hc ha hb'
    let x:= i.a; let V:= W.V x;let n:= i.b; let N:=P.N i.a; let Z:= destination V N n
    have H':= frozen_waltz q h v a hs ht hb C P hc hx i; have hu:Court o F (bornY ρ W a F T q.horizon x N (n+1)):= birth a v q hs ht hb _ _ _ i.ups.zone (i.ups.cap.trans (hc _)); let L:= Lab.saga ρ a W x N (n+1); have hK:i.b<N:=i.head.trans_le (hc i.a)
    let M T:= migrates (D:=D) a Z (W.wood x n) K L ρ (W.toEmpire.bill _ _) (growL _ _) d l T
    have hv : q' i.bed=U i*ᵥ q' i.ups:= by
        have H'' := migration F H q.horizon (bornY ρ W a F T q.horizon x N (n+1)) hu Z (W.wood x n) (W.toEmpire.bill x n) L ((genu V (W.wood x) (W.toEmpire.bill x) _ a v hs hK).toStory) ρ v (V.clock.adm _) (quota_fits q i.toLeaf) (growL _ _) a _ (hA i.ups) l le_rfl
        change clover F (location V N n) _ (A i.bed) l= _; rw [loc_land _ _ _ hK,show A i.bed=M (A i.ups) from H'.symm]; exact H''
    rw [hv,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (tagBack (ha i)).1,Matrix.one_mulVec]
-- display at top or at any Corona end.
lemma fresnel (x:Letter F): Faint τ (fun i=> g i * Degree θ (startP i C)) (fun i=>
   clover F (location (W.V i) (P.N i) (C.N i)) K.penalty (Y i) l x - ((WLocal W a ρ F T q.horizon (peak C i).toLeaf (P.N i))*ᵥ (fun j:Letter F=> coeff 0 (afloat l T ρ Y q a C P i j ()))) x) := by
   have hh := Winside q h p c a v hs ht hb hR hl hr hr' C P hc hp hx hz hw x; apply (hh.link (peak C)).lower; intro i
   let V:=location (W.V i) (P.N i) (C.N i);let A:=afloat l T ρ Y q a C P i
   let R:= bornY ρ W a F T q.horizon i (P.N i) (C.N i); let S:=larch R A (); let k:=max d l
   have hJ:Court o F R:= birth a v q hs ht hb i (C.N i) (P.N i) (C.land i) (hc i)
   have hr j: Clef o (R j) k:= clef_through (hJ.officers j) ((slotsFits F j).trans (le_max_left ..));
   have hS:Clef o S k:= Clef.sum Finset.univ _ fun i _=> (hr i).launch _
   let X (T : Anthem D G)(l:ℕ):=clover F V K.penalty T l x
   let X':= calmTop l T ρ Y q a C P (peak C i)
   have hg:= calm_yes q h a v hs ht hb C P hc hx (peak C i)
   have hv : X (Y i) l=X X' l+X S k:= by
       have he T u (h : Wade o T u)(hu:u≤ k): X T u=X T k:= by unfold X clover;rw [upper_king V K.penalty _ h k hu]
       rw [he _ l (hx i).fare (le_max_right ..),he _ l hg.fare (le_max_right ..)]
       have hp : X'+S=Y i:= by rw [show X'=Y i-S from stitches .., sub_add_cancel]
       exact (congr_arg (fun t=>X t k) hp.symm).trans (clover_plus F _ K.penalty_pos ((W.V i).clock.adm _) (Spigot.from_clef (clef_through hg (le_max_right ..)) 0) (Spigot.from_clef hS 0) x)
   have hQ : X S k = ((Woven F V K.penalty R)*ᵥ (fun j:Letter F=> coeff 0 (A j ()))) x:= by
       change clover F V K.penalty (larch _ _ _) k x= _; rw [clover_align F V K.penalty_pos ((W.V i).clock.adm _) R A hr]; unfold Matrix.mulVec dotProduct; refine Finset.sum_congr rfl fun j _=>?_ ; change X (R j) k * _=X (R j) d*_; congr 1;unfold X clover; rw [upper_king V K.penalty _ ((hJ.officers j).fare.through (slotsFits F j)) k (le_max_left ..)]
   change |X _ l - ((Woven F V K.penalty R)*ᵥ _) _|≤ |X X' l|; rw [hv];exact (le_of_eq (congr_arg abs (by rw [hQ]; exact add_sub_cancel_right ..)))


end YM.FormalBulk08.Tundra
