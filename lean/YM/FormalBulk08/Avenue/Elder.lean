import YM.FormalBulk08.Avenue.Ancestry
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
open Trellis Aster Dove Quire Clover Elm North
open Dove.Lab
variable {I:Type}{K:KernelChoices}{W:Lab G K I}
open Spruce
variable {E R:ℕ}{ρ:ChartRatio G}{F:Frame G d}{T:SectionData F}{H:Source.Hol G} {Y: I→Anthem D G} {z:I→ℝ}{θ:ℝ}{τ:Time I}
variable (q:Quota F H W o D E R) (h:Use W ρ E) (u:Extras W) (a: hue G)(v:LocalRatio ρ)(hs:G.Simple)(ht:T.Sound H)(hb: Bid.pop T)(hR:d≤ R)(hl:l≤ R)(hr:θ<1/2)(hr':0≤θ)(C P:Pin W.scrolls)(hc:∀ i,C.N i≤ P.N i) (hp: Erudit τ W.scrolls C)(hx:∀ i,Clef o (Y i) l)(hz:∀ i,0≤z i)(hw:∀ e≤E,∀ r, Tender ((sage C).reach (peak C)) o (fun i=>W.eagle (peak C i)) z (fun x p=>Y x p e r))
abbrev coastEye (l:ℕ)(i:Deck C) (F:Frame G d) (Y:Anthem D G) := clover F (location (W.V i.a) (P.N i.a) i.b) K.penalty Y l
include h q a v hs ht hb hc hx hw hz
lemma calm_paid (i:Deck C) : Clef o (calmTop l T ρ Y q a C P i) l:= by
    have hh k:= tender_qual hz hw k; have ht':= confidential q h v a hs ht hb C P hc hx hh i; exact ht'.1.sub (larch_cleared _ _ (winged q h v a hs ht hb C P hc hx hh i) ((birth a v q hs ht hb _ _ _ i.zone (i.cap.trans (hc i.a))).officers) ())
include hp hR hl u hr hr'
lemma Wwithin (x:Letter F):
    let Q:=fun i:Deck C=> coastEye C P l i F (calmTop l T ρ Y q a C P i)
    Faint (rday τ C) (fun i=>z i.a*Degree θ (startP i.a C)) (fun i=> Q i x):= by
    intro q'; let f i:= z i*Degree θ (startP i C);
    have ht' (i:Turn C):= (mat_begins a v q hs ht hb i.a i.b (P.N i.a) i.zone (i.head.trans_le (hc i.a))).1; let U(i:Turn C):= noncontract F (echoR T ρ q a C P i)
    let Q'(i:Turn C):= echoR T ρ q a C P i; let b(i: Turn C)(x):=heightK ((W.V i.a).S.block i.b) d (Pose.weight F x)
    have ha i: Found (slots F) (Pose.weight F) (tag (U i)) (b i):= nc_stamp (Q' i) _ (ht' i); have hb'(i:Turn C) j:1≤ b i j:= crown_weight ..
    let A i:= calmTop l T ρ Y q a C P i
    have hA i:=calm_paid q h a v hs ht hb C P hc hx hz hw i
    have hf i:0≤f i:=mul_nonneg (hz i) (ratioR_pos ..).le
    have hJ:=tabular hp.origin hp.depth h.liable
    refine faint_forward (Q:=q') (b:=fun i j=>(b i j)⁻¹) (T:=fun i=>(U i)⁻¹) (w:=Pose.weight F) (s:=Pose.slots F) (fun i=>?_ ) (?_) (?_) (?_) (fun i j=> inv_le_one_of_one_le₀ (hb' i j)) hf (raySteps hp.depth) _
    rotate_left
    · intro i; rw [(tagBack (ha i)).2]; exact primes (ha i)
    · intro y
      let s:=fun i=> startP i C;let g i:= calmTop l T ρ Y q a C P (s i); let N(k:I):=P.N k; let R' i:=location (W.V i) (N i) (W.neck i); let B i:= mediumP G K ((W.V i).clock.J (W.neck i)); let A' i:= bandP G (R' i) K.penalty; let η i:= W.windowD (s i).toLeaf
      have he i: Fees G K ((W.V i).clock.J _) (B i):= fee_live G K _ ((W.V i).clock.adm _)
      have hp':Soft τ B:= town_fold (g:=fun i:I=>(s i).toLeaf) hp.origin u
      have hw' e r (hx':e ≤ E): Tender τ o η f (fun i p=>g i p e r) := tenderLift (p:=s) (soft_day τ) (show Tender _ o W.eagle (fun i:Deck C=> z i.a*Degree θ i) (fun i p=>A i p e r) from (southbound q h v a hs ht hb C P P hc (fun _=>le_rfl) hl hR hz hx hx (fun j hj k=> Matched.constant (hw j hj k)) hp hr hr' hx' r).left)
      have hT t:Tender τ o η f (fun i p=>winner (R' i) K.penalty l (g i) p t):=(stature_pay (o:=o) (δ:=fun _=>0) (A:=A') (L:=A') (T:=fun i p=>g i p 0) (S:=fun i p=>g i p 0) hp' (fun i=>(he i).active) (fun i=>(h.zero (s i).toLeaf).le) (fun _=>le_refl _) (fun i j k=> (he i).cords _ _ _) (fun i j k=> (he i).cords _ _ _) (fun i j k=>by simp) (fun r=>Matched.constant (hw' 0 r (Nat.zero_le _))) (r:=t) l).left
      obtain ⟨Z,hp1,b,hP⟩:= hT (slots F y); let m:= amounts F H W o D E R; have hp2:= town_fold (g:=fun i:I=>(s i).toLeaf) hp.origin q.running
      let u:= Pose.inside F y D
      refine ⟨_, hp2.times (hp1.times (soft_coin τ ‖u‖)),fun i=> mul_nonneg (q.supply h (s i).toLeaf).plus (mul_nonneg (b _) (norm_nonneg _)), fun i=>?_⟩; refine (((q.supply h (s i).toLeaf).pupils _ ((slotsFits F y).trans (by omega))).pays _ _ (hP i u) y).trans_eq ?_;ring
    · have hc(i j:Letter F): Soft (qday τ C) (fun x=> coeff 0 (Q' x i j)) := by
         let g (x:Turn C):transferPoint W:=⟨x.toLeaf,P.N x.a,P.N x.a,x.head.trans_le (hc x.a),le_rfl⟩; exact town_fold (g:=g) (hJ.reach (fun i:Turn C=>i.bed)) ((staccato q h v hs ht hb a hR i j 0 (Nat.zero_le E)).left)
      exact nc_invoice hc ha hb'
    let x:= i.a; let V:= W.V x;let n:= i.b; let N:=P.N i.a; let Z:= destination V N n
    have H':= waltz q h v a hs ht hb C P hc hx (tender_qual hz hw) i; have hu:Court o F (bornY ρ W a F T q.horizon x N (n+1)):= birth a v q hs ht hb _ _ _ i.ups.zone (i.ups.cap.trans (hc _)); let L:= Lab.saga ρ a W x N (n+1); have hK:i.b<N:=i.head.trans_le (hc i.a)
    let M T:= migrates (D:=D) a Z (W.wood x n) K L ρ (W.toEmpire.bill _ _) (growL _ _) d l T
    have hv : q' i.bed=U i*ᵥ q' i.ups:= by
        have H'' := migration F H q.horizon (bornY ρ W a F T q.horizon x N (n+1)) hu Z (W.wood x n) (W.toEmpire.bill x n) L ((genu V (W.wood x) (W.toEmpire.bill x) _ a v hs hK).toStory) ρ v (V.clock.adm _) (quota_fits q i.toLeaf) (growL _ _) a _ (hA i.ups) l le_rfl
        change clover F (location V N n) _ (A i.bed) l= _; rw [loc_land _ _ _ hK,show A i.bed=M (A i.ups) from H'.symm]; exact H''
    rw [hv,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (tagBack (ha i)).1,Matrix.one_mulVec]
-- display at top or at any Corona end.
lemma highW (x:Letter F): Faint τ (fun i=> z i * Degree θ (startP i C)) (fun i=>
   clover F (location (W.V i) (P.N i) (C.N i)) K.penalty (Y i) l x - ((WLocal W a ρ F T q.horizon (peak C i).toLeaf (P.N i))*ᵥ (fun j:Letter F=> coeff 0 (afloat l T ρ Y q a C P i j ()))) x) := by
   have hh := Wwithin q h u a v hs ht hb hR hl hr hr' C P hc hp hx hz hw x; apply (hh.link (peak C)).lower; intro i
   let V:=location (W.V i) (P.N i) (C.N i);let A:=afloat l T ρ Y q a C P i
   let R:= bornY ρ W a F T q.horizon i (P.N i) (C.N i); let S:=larch R A (); let k:=max d l
   have hJ:Court o F R:= birth a v q hs ht hb i (C.N i) (P.N i) (C.land i) (hc i)
   have hr j: Clef o (R j) k:= clef_through (hJ.officers j) ((slotsFits F j).trans (le_max_left ..));
   have hS:Clef o S k:= Clef.sum Finset.univ _ fun i _=> (hr i).launch _
   let X (T : Anthem D G)(l:ℕ):=clover F V K.penalty T l x
   let X':= calmTop l T ρ Y q a C P (peak C i)
   have hg:= calm_paid q h a v hs ht hb C P hc hx hz hw (peak C i)
   have hv : X (Y i) l=X X' l+X S k:= by
       have he T u (h : Wade o T u)(hu:u≤ k): X T u=X T k:= by unfold X clover;rw [upper_king V K.penalty _ h k hu]
       rw [he _ l (hx i).fare (le_max_right ..),he _ l hg.fare (le_max_right ..)]
       have hp : X'+S=Y i:= by rw [show X'=Y i-S from stitches .., sub_add_cancel]
       exact (congr_arg (fun t=>X t k) hp.symm).trans (clover_plus F _ K.penalty_pos ((W.V i).clock.adm _) (from_clef (clef_through hg (le_max_right ..)) 0) (from_clef hS 0) x)
   have hQ : X S k = ((Woven F V K.penalty R)*ᵥ (fun j:Letter F=> coeff 0 (A j ()))) x:= by
       change clover F V K.penalty (larch _ _ _) k x= _; rw [clover_align F V K.penalty_pos ((W.V i).clock.adm _) R A hr]; unfold Matrix.mulVec dotProduct; refine Finset.sum_congr rfl fun j _=>?_ ; change X (R j) k * _=X (R j) d*_; congr 1;unfold X clover; rw [upper_king V K.penalty _ ((hJ.officers j).fare.through (slotsFits F j)) k (le_max_left ..)]
   change |X _ l - ((Woven F V K.penalty R)*ᵥ _) _|≤ |X X' l|; rw [hv];exact (le_of_eq (congr_arg abs (by rw [hQ]; exact add_sub_cancel_right ..)))

end YM.FormalBulk08.Avenue
