import YM.MS.Swirl.Unpack
/-!
# Endµ mark billing glyphs and fonts
 Stripped kernels actual products; membership and parity; Tether proof leg-wise.
 Unprojected canonical seeds for MStencils spelled with same η reader.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl.Near
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom
open scoped Topology ContDiff Interval
variable {A E I W:Type} [AddCommGroup E][Module ℂ E] {G:Gauge}{i:I}{L:I→Side}{A':Faces I} {φ:Team}{n d:ℕ}{N:Side} {X:Actor G} {V: W→Actor G} [LinearOrder W] {b:Bool}{η:I→ℝ}
open SpaceOut
lemma billRent {B:Local.Physical.Deck G}(P: LitBook B)(p:Team)(v: Acts B d): Circle G ( Menus.rent P p v ) false 0 where
    stance0 _ _ h:=Bool.noConfusion h
    actual i x:= poses P p ..
    settled i x:= appears P p v x i
    tag i:= rentReady P p ..
    room i:=⟨ i+d,fun x=> by exact_mod_cast rentLimit P p v x i⟩
-- seed physical product at anchor A+c. not average. literature normalization of effective lid.
abbrev Mark_T (G:Gauge)(N:Side)(A x:Cover): Linear ( Dot G Cover ) ( BL (FixedMode G N) ):= ( Orbit.anchor G N A ) ∘ₗ frameL x ∘ₗ Tone.run
def Marks (V: W→Actor G)(x:ℝ)(N:Side)(A: Cover)(c:W→ Cover): Mate (FixedMode G N) W:= fun s=> if h:s.Nonempty then if s.card=1 then pointL ℕ ( Mark_T G N A (c ( s.min' h )) ) ( V ( s.min' h ) x ) else 0 else 0
lemma mark_me (x:ℝ)(N:Side)(A:Cover)(c:W→Cover)(v:W): Marks V x N A c {v}=pointL ℕ ( Mark_T G N A ( c v ) ) ( V v x ):= by simp [Marks]
lemma mark_off {s:Finset W}(h:s.card≠1)(x:ℝ)(N:Side)(A:Cover)(c:W→Cover): Marks V x N A c s=0:= by unfold Marks; split <;> rfl
variable (c:Berth ( W:=W ) ( I:=I )) (i:I) {s: Finset W}
set_option quotPrecheck false
local notation "D'"=> dimT L i
local notation "Β"=> κP G (dimT L i) b
abbrev ΓM (c:Berth ( W:=W ) ( I:=I ))(L:I→Side)(i:I)(η:I→ℝ)(A':Faces I)(V:W→Actor G):= Marks V ( η i ) (dimT L i) ( A' i ) (fun w=> c w i)
local notation "Μ'"=> ΓM c L i η A' V
lemma payM_seed : W0 L b (goalsK c η V) i A'= Β ∘ Μ':= by
   funext s k; by_cases hz:s.card=1; · obtain ⟨v,rfl⟩:=Finset.card_eq_one.mp hz; change Aspect _ _ _ _ _= Β (Marks V _ _ _ _ {v}) k; rw [ goals_m,mark_me ]; rfl
   rw [Function.comp_apply, show Μ' s=0 from mark_off hz ..,map_zero]; change Aspect _ _ _ _ ( goalsK c η V s k i )=_; rw [goals_t _ _ hz]; simp only [Pi.zero_apply,map_zero]
lemma normPay : Font σbranch (W0 L b (goalsK c η V) i A') s= Β ( Font σbranch Μ' s ):= by rw [ payM_seed ]; exact ( lore ( S:=iota G ( dimT L i ) ) ( b:=b )|>.figure ( Puff.SplitP.marked W ) Μ' s )|>.symm
-- migrate marks φ.γ fee
omit [LinearOrder W] in
lemma frameSym (f: Cover)(H: Law G)(hp: Symm DotFlip H): Symm DotFlip ( frameL f H ):= by
    rw [ f_l ]; intro l i j r; simp_rw [ lodg,sleeve_here ]; rw [ hp l i j, show net (l++i::j::r)=_ from ( rfl : net ( l++i::j::r )=_) ]; -- replacement
    unfold hook; simp only [net_append,net_cons,List.map_append,List.map_cons,List.prod_append,List.prod_cons ]; rw [add_left_comm i.2 j.2]; ring -- bind treatment
omit [LinearOrder W] in
lemma anchorSym (a:Cover)(H:Law G)(hp:Symm DotFlip H): Symm (σbranch ( n:=N )) ( anchor G N a H ):= by intro l i j r; rw [chase_now,chase_now]; simp_rw [Orbit.point, Orbit.stage,net_append,net_cons,List.map_append,List.map_cons,hp (l.map addr) ( addr i ) ( addr j ), add_left_comm i.2 ]; exact mul_left_comm ..
omit [LinearOrder W] in
lemma feeL (H: Dot G Cover)(A q:Cover)(h:Tuned H 0)(hv:Limit H.val (n:ℤ)): Mark_T G N A q H∈ FeeP (σbranch ( n:=N )):= by
    refine ⟨anchorSym A _ (frameSym q _ ( tied.sym H h.symm)),?m⟩; apply minH ( v:=( n:ℤ ) ); apply ( Orbit.gl_A G N A ).lap _ n; intro l hl; rw [ LinearMap.comp_apply,f_l, lodg,sleeve_here, Tone.oneRank hv _ hl,mul_zero,mul_zero ]
lemma momentΓ (V:W→Actor G)(A':Faces I)(η:I→ℝ)(L:I→Side)(h: Badge V): Γ ( Font σbranch (ΓM c L i η A' V) s ) σbranch:= by
    suffices hp:( Font σbranch (ΓM c L i η A' V))∈ allIndex ( allIndex ( FeeP (σbranch ( G:=G ) ( n:=dimT L i )) ) ℕ ) ( Finset W ) by exact hp s ( Set.mem_univ _ )
    let M':= PermV (σbranch ( G:=G ) (n:=dimT L i)); have hz : Γ M'.unit σbranch:= refineπ useN (coin 1) feeUnit; refine costCheer ( Puff.SplitP.marked W ) hz ( fun _ h _ hv=> ΤΓ_pair h hv ) ?_; intro s _; by_cases hs:s.card=1; · obtain ⟨v,rfl⟩:= Finset.card_eq_one.mp hs; unfold ΓM; rw [mark_me]; intro k _; obtain ⟨c',hc⟩:= ( h v ).room k; exact feeL _ _ _ ( (h v).actual k (η i) ) ( hc (η i) )
    unfold ΓM; rw [mark_off hs]; exact ( allIndex ( FeeP (σbranch ( G:=G ) ( n:=dimT L i )) ) ℕ ).zero_mem
-- hom α.D_γ from proof. U input full and adjusted γ.
variable {Xv:W→Actor G}
omit [LinearOrder W] in
lemma Mark_f (t:Team)(x:ℝ)(F:Dot G Cover)(k:ℕ)(N:Side)(A q:Cover): Mark_T G N A q ( train (Y t x) k F )= merit ( inUse t x ) k ( Mark_T G N A q F ):= by
    ext l; unfold Mark_T; rw [ offer ]; change Orbit.anchor G N A ((frameL q) _ ) _= _ * Orbit.anchor G N A ((frameL q) _ ) _; rw [ Fleet.spell_anchor,Fleet.spell_anchor,f_l,f_l ]; simp_rw [lodg,sleeve_here,runner,offer,stake]; ring
lemma Mark_T_shift (t:Team)(x:ℝ)(F:T (Dot G Cover))(N:Side)(A q:Cover): pointL ℕ ( Mark_T G N A q ) (car (Y t x) F)=taxi ( inUse t x ) ( pointL ℕ ( Mark_T G N A q ) F ):= by funext k; change Mark_T G N A q _ = _; rw [rolls,map_sum ]; exact Finset.sum_congr rfl fun _ _=> Mark_f ..
def Changes (V X: W→ Actor G)(t:Team): Prop:= ∀ w (x:ℝ), V w x = car ( Y t x ) ( X w x ) -- V adjusted
lemma marΓ (h:Changes V Xv φ): Μ'= taxi ( inUse φ ( η i ) ) ∘ ΓM c L i η A' Xv:= by
    funext p; unfold ΓM Marks; by_cases hp:p.Nonempty; swap; · rw [ dif_neg hp ]; simp_rw [Function.comp_apply,dif_neg hp,map_zero ]
    rw [ dif_pos hp ]; simp only [Function.comp_apply,dif_pos hp ]; split; rw [h,Mark_T_shift]; exact ( map_zero _ ).symm
lemma translate (h:Changes V Xv φ): Font σbranch Μ' s= taxi ( inUse φ (η i ) ) ( Font σbranch ( ΓM c L i η A' Xv ) s ):= by rw [marΓ c i h]; exact Eq.symm ((show Tether ( taxi ( inUse φ (η i) ) ) ( PermV σbranch ) ( PermV σbranch ) from ⟨ taxiUnit _,fun _ _=> metra _ ⟩).figure (Puff.SplitP.marked W) ( ΓM c L i η A' Xv ) s)
-- Changes for all rent
omit [LinearOrder W] in
lemma oil_roll (t:Team)(x:ℝ)(U:T ℂ)(f:T (Dot G Cover)): pairW (LinearMap.lsmul ℂ ( Dot G Cover )) U ( car ( Y t x ) f )= car ( Y t x ) ( pairW ( LinearMap.lsmul ℂ ( Dot G Cover ) ) U f ):= by
    funext i; simp_rw [ paired,rolls,paired,LinearMap.lsmul_apply,map_sum,Finset.smul_sum,map_smul ]; exact Puff.Engine.rewrap useN (Dot G Cover) (fun i j k=> U i • train (Y t x) j (f k)) i
omit [LinearOrder W] in
lemma rankV {B:Local.Physical.Deck G}(t:Team)(U:LitBook B)(d:ℕ)(A:Acts B d)(x:ℝ): Menus.rent U t A x= car ( Y t x ) ( Menus.rent U (Stripped t) A x ):= by
    have he (t:Team): Menus.rent U t A x=∑ i:Glyph B d,pairW ( LinearMap.lsmul ℂ (Dot G Cover) ) (fun n=> oil A i n x) (Glyph.preamble U t i x):= funext (fun n=> by rw [Finset.sum_apply]; rfl);
    rw [ he t, he ( Stripped t ),map_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Glyph.preamble; rw [ sWob ( t:=t ), oil_roll ]
end YM.MS.Swirl.Near
