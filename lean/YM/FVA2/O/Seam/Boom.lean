import YM.FVA2.O.Seam.Cross
/-!
# Crossing estimates between the full input product and one remote exterior

Handle crossings in the different length ranges. In particular on the sub-unit
side use `thorns`: the full product is up to a rapidly-decaying `Sweep` error
a simple unanchored product, with no extra connected-insertion terms. Hence
compute with `thicket` (not only `woods`) in `fieldV`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse
open scoped Topology ContDiff Interval
variable { G: Gauge } {α W I :Type} { S:Home α I }{ P:Geo I } {F H X:T ( Glade G I )}{a:I→QP}{u:ℤ}{b:Label _}
variable {B:Deck G}{K:Booked B}{M:MS_Data G K}{r: Label B}
lemma zero_reps (ht:Reps F 0 (Station P)): ∀ i,Lend ( Mid P ) P ( F i ):= by
    intro i; refine ⟨0, Mid.way.lease (ht i) tar_nn ?_⟩; rw [tar_zero]; ext; simp only [ Function.comp_apply,neg_zero,zpow_zero ]; rfl
variable [LinearOrder W]{x:Position W I}{R: W→ Label B}{s: Finset W}
-- generic
lemma scout (h:Grass S P)(hp:liveP S P.η)(hv:separable x)(hs:Banks H u)(hf: Calm S P H) {L:MH ( T ( Glade G I ) )} (hL:∀ {q:ℤ}{X Y}, Banks X 0→ Banks Y q→ L (bond G I X Y)=bond G I (L X) Y+bond G I X (L Y)) (hx:∀ i∈s, Chaff S P ( L ( singletonM P M ( x i ) ( R i ) ) ) )(hk:Chaff S P (L H)): Chaff S P ( L (rootT P M x R s H) ) := by
    induction s using Finset.induction_on with
    | empty=> rw [R_nil]; exact hk
    | insert i s hi ih=>
        let V:= woods P M x R s; have he := (Certified_single ( p:=x i ) (P:=P) ( M:=M ) ( R i )).1.life; rw [ R_step hv i hi,hL he ( R_bank hv hs s ) ]; exact ( Chaff.badges (hx i (by simp)) ( Calm.bonds h ( Calm_W hv hp s ) hf ) ).add ( Chaff.pass ( priceT hp ) ( ih ( fun j hj=> hx j (mem_insert_of_mem hj) ) ) ) -- defeq
variable {η:I→ℝ}
def flatten (P:Geo I) : Geo I:= ⟨ 0,P.η,fun _=>le_rfl⟩
abbrev thins (P: Geo I)(M: MS_Data G K)(x:Position W I)(R:W→ Label B)(s:Finset W):= thicket P M x R s-woods P M x R s
lemma thins_mem (hp:separable x): Banks (thins P M x R s) 0:= fun i=> ( (firm hp).1.life i ).sub ( W_bank hp _ i )
omit [LinearOrder W] in
lemma far_ne {p:I→QP} (h:CoverSep P ( p-a ))(i:I): p i≠a i:= by obtain ⟨C,hC,k⟩:= h.floor; exact sub_ne_zero.mp ( norm_pos_iff.mp ( (mul_pos hC (exp_pos _)).trans_le (k i) ) )
omit [LinearOrder W] in
lemma mesh_sep (h:Mesh P x): separable x := by intro i j k hj; by_contra ht; exact far_ne ( h j k ht ) i hj
lemma thorns (hp:Mesh (flatten P) x)(he:∀ i,Cool.Fixed ( x i )): Sweep P ( thins P M x R s ) := by
    obtain hh:= sents ( P:=flatten P ) hp rfl ( serves ( P:=flatten P ) ( M:=M ) ( r:=R ) ( mesh_sep hp ) ) he s; exact hh
lemma midships (hp:Mesh (flatten P) x)(he:∀ i,Cool.Fixed (x i)): Reps (thicket P M x R s) 0 (Station P) := by
    intro i; obtain ⟨ p,hp,Z,hZ,hu,h⟩:= field_whole hp rfl he ( serves ( P:=flatten P ) ( M:=M ) (r:= R) ( mesh_sep hp ) ) s (i+1) 0; let F:= thicket P M x R s; let V:= Physical P.η M p+nav M P.η Z; change Colorable ( Station P ) ((F-Physical P.η M p)-nav M P.η Z) (i+1) 0 at h; rw [sub_sub] at h; change Reps Z 0 ( Station P ) at hu;
    have hv : Reps V 0 ( Station P ):= Reps_add ( PH_V liveS.allow ( show Valid (Station P) p from hp ) ) ( Reps_desc ( RVA liveS.allow ( show Response Z M P.η (-1) from hZ ) hu ) (by omega) ); obtain hh:= hv i; obtain h0:= h i ( Nat.lt_succ_self i ); suffices ht : Latch.Lease false false _ (sweep (Station P) (((F-V)+V) i)) (fun p=> (Station P).primary.length p ^ (-(0:ℤ))) by rw [sub_add_cancel] at ht; exact ht
    refine Latch.Lease.plus ( Latch.Lease.sticks h0 ?_ ) hh; intro p; dsimp only [decay]; simp only [ Nat.cast_zero, neg_zero,zpow_zero,one_mul ]; exact exp_le_one_iff.mpr ( mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p_gain.le) ( show 0 ≤ t p from p.ge ) ) -- decay flat
omit [LinearOrder W] in
lemma shareToe (hp: Banks F 0): Share G I F ( glaze G I ).unit=0:= by obtain h:= share_graft ( Y:=(glaze G I).unit ) ( hedge hp ) ( hedge ( Fuse.unitC (G:=G) (I:=I) ) ) ( Fuse.unitC ( G:=G ) ( I:=I ) ); let L:=glaze G I; change Share G I F (L.core L.unit L.unit)= L.core _ _+L.core _ _ at h; rw [ L.identityK,L.identityR,L.identityK ] at h; exact ( add_right_inj ( Share G I F L.unit ) ).mp ( by rw [add_zero]; exact h.symm )
lemma shareProbe (h:Grass S P)(hp: liveP S P.η)(he:separable x)(ht: Calm S P H)(hB:Banks H u)(hx: ∀ i∈s,CoverSep P ( a - x i ) )(hV: Chaff S P ( Share G I ( singletonM P M a r ) H )): Chaff S P ( Share G I ( singletonM P M a r ) ( rootT P M x R s H )) := scout h hp he hB ht ( fun he h=> share_graft ( hedge ( ( Certified_single ( p:=a ) ( M:=M ) ( P:= P ) r ).1.life ) ) ( hedge he ) h ) ( fun i hi=> shareF h hp ( hx i hi ) ) hV
lemma touchProbe (h: Grass S P)(hp:liveP S P.η)(he:separable x)(ht:Calm S P H)(hB:Banks H u)(hx:∀ i∈s,CoverSep P ( a-x i ) )(hV: Chaff S P ( Touch G I ( singletonM P M a r ) H )): Chaff S P (Touch G I ( singletonM P M a r ) (rootT P M x R s H)):= scout h hp he hB ht (fun he h=> touch_graft (hedge (( Certified_single (p:=a) (M:=M) ( P:= P ) r).1.life)) (hedge he) h) (fun i hi=> touchF h hp ( hx i hi )) hV
lemma share_wood (ht: liveP S P.η)(hp: Grass S P)(h:separable x)(he: ∀ i∈s,CoverSep P ( a-x i )): Chaff S P ( Share G I ( singletonM P M a r ) ( woods P M x R s ) ):= by
    let F:= woods P M x R s; let H:= (glaze G I).unit; rw [show woods P M x R s=rootT P M x R s H from (glaze G I).identityR F |>.symm ]; exact shareProbe hp ht h (fun i=> ⟨0,(by unfold Pays; rw [tar_zero]; exact totalUnit i)⟩ ) ( Fuse.unitC ) he ( by rw [ show Share G I _ H=0 from shareToe ( ( Certified_single ( p:=a ) ( P:=P ) ( M:=M ) r ).1.life ) ]; exact Chaff.zeros )
variable (h:Mesh (flatten P) x)(ht: ∀ i,Cool.Fixed ( x i ))
include h ht
lemma thinsFine (i:ℕ): Lend (Litt P) P ( thins P M x R s i ):= by
    obtain hp:= thorns ( s:=s ) ( M:=M ) ( R:=R ) h ht i 0; refine ⟨0,Latch.Lease.sticks hp ?_⟩; intro i; unfold Cool.stamp; rw [ zpow_zero, tar_zero ]; rfl
lemma fieldV (hx: CoverSep P a)(hp:∀ i∈s,CoverSep P (a - x i)): Chaff ( deckB P ) P ( Share G I ( singletonM P M a r ) ( thicket P M x R s )):= by
    intro i; apply Tiny.section; swap; · exact ShareE Mid.grass Mid.live hx ( firm ( mesh_sep h )|>.1.life ) ( zero_reps ( midships h ht ) ) i -- grammar invocation argument order
    let F:= thins P M x R s; let X:= woods P M x R s; rw [ show thicket P M x R s=F+X from (sub_add_cancel ..).symm, map_add ]; exact Chaff.add ( ShareE Litt.grass Litt.live hx (thins_mem ( mesh_sep h )) ( thinsFine h ht ) ) ( share_wood Litt.live Litt.grass (mesh_sep h) hp ) i
lemma thicket_T : Calm ( deckB P ) P ( thicket P M x R s ):= by
    intro i; apply season; swap; · exact Earn ( zero_reps ( midships h ht ) i )
    let F:= thins P M x R s; let X:= woods P M x R s; rw [ show thicket P M x R s= F+X from (sub_add_cancel ..).symm ]; exact Tame.add Litt.grass ( Earn ( thinsFine h ht i ) ) ( Calm_W (mesh_sep h) Litt.live s i )
end YM.FVA2.O.Seam
