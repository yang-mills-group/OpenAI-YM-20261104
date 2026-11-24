import YangMills.WilsonProof.NativeSupport.YM.MS.Halo.Madd
import YM.MS.Image.Globe
import YM.MS.Wind.MatchM
/-!
# Bulk satisfies `Compact.Q` & `Badge`. L Wilson comparison can be formed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Halo
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Train Pearl Motif Alps Native Outlook High Detect Mark -- conflict shadow
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge}{m n k:ℕ}{b:Bool}{X:T (Flats G)}{p:T (Coat G)}{z h:ℂ}{r t:ℤ}{F:Mob G}
lemma pulse1 (G:Gauge): pulseX G 1=B₁ G:= by simp [pulseX, Literal.hiss,χ]
lemma fund_one (G:Gauge)(m:ℕ) : Pace (pulseX G 1 m) 4 0 3:= by rw [pulse1]; exact B₁_P ..
lemma funded (n:ℕ)(G:Gauge)(m:ℕ): Pace (pulseX G n m) 4 0 4:= by
   rcases n with _|(_|(_|k)); simp_rw [Up0]; exact Pace.zero; exact (fund_one G m).taller (by decide); rw [show pulseX G 2=B₂ G by simp [pulseX,Literal.hiss,χ]]; exact B₂_P ..; rw [show pulseX G (k+1+1+1)=0 by simp [pulseX, Literal.hiss,χ,Finsupp.single_eq_of_ne (show k+1+1+1≠2 from by omega)]]; exact Pace.zero
lemma Pace.homer (he:∀ m, Pace (F m) k t r): Home F k:= fun u=>funext (fun i=> funext (fun l=> (he i).home l u))
lemma Pace.priceV (he:∀ i,Pace (F i) k t r): kPrice F:= fun i E _ _ _=> (he i).price E
lemma Pace.prepay (he:∀ i,Pace (F i) k t r)(hp: Sturdy b F)(hv:ShadeG F): Badge b (fun _=>F) k t:= by
   have ht:=priceV he; refine ⟨fun _=>homer he, r, ⟨?_,?_,?_⟩,?_⟩; exacts [ ⟨Shine.mer.uLive (Live.stays ht), Eventually.of_forall fun i=> hp ⟩, Eventually.of_forall fun _=> (show Collar t _ from ⟨fun i=>(he i).sym,hv,fun i=>(he i).ghost⟩), (show realAlong _ _ from Eventually.of_forall fun _ x=>(he x).sense), Eventually.of_forall fun _ x=>(he x).up ] -- look namespaces
lemma invest (G:Gauge): Schema true 0 4 (gloss (pulseX G)):= fun n=> Pace.prepay (funded n G) (Surf.eu _) (folk n)
-- `Compact`: earliest cubic tensor from quantum leader sufficient. explicit test actual normalized.
lemma lining (he:∀ i, Pace (F i) n t r)(hx:ShadeG F): Solid b (F 0) t := ⟨fun l i j k _=> (he 0).sym l i j k, fun v _ hv=>(he 0).ghost v hv,fun w _ p=>congr_fun (hx 0 p) w,fun w _=> (he 0).sense w⟩
lemma snTag (he:∀ i,Pace (F i) n t r): Form (F 0) wfield n b:= by
   have hz : F 0=Tad F n 0:= congr_fun (Home.complete (Pace.homer he) (Pace.priceV he)) 0; rw (occs:=.pos [1]) [hz]; exact skin_form _ _ (fun E _ _ w _=> (BigG ( Pace.priceV he ) 0 w).smooth ())
lemma potatoes (i:ℕ)(w:Legs (Shore G i))(ht:net w=0): (Wick.Q G i).raise (pulseX G 1 i) w=0:= by
   obtain hx:= wisdom 1 i w (fun _=>ht); rw [BasisC, paired] at hx; simp [ Finset.Nat.sum_antidiagonal_succ, Up0 ] at hx; exact hx
lemma Crown (G:Gauge): Class (pulseX G 1 0) 4 := ⟨ lining (fund_one G) (folk 1),potatoes 0, snTag (fund_one G), Outlook.lane (Surf.eu 1) ⟩ -- class name?
-- compute token in S* by variation using Moss at arbitrary z.Op.Hasterm
lemma Captain (a:Chan G n)(p:SectorP n)(w:Legs (Shore G n)) : ploy G h n ((onX true a,p)::w)= phase a * applyS h G n a w:= by
   unfold ploy; change ( ( Motif.core G n h ) ((_,p)::w)+(cape _) _ )= _; rw [ show Motif.core G n h ((onX true a,p)::w)=0 from congr_fun ((core_g h).2.1 a p) w, zero_add,D_eval _ (cape _),cape_tick (application h)]; rfl
lemma plea (j k l:G.ColorIndex):
    Sc h G n j [ (onX false (none,k),0),(onX false (none,l),0) ] = -h*rune k l j := by
       unfold Sc; simp only [Pi.smul_apply,smul_eq_mul, chew, Finset.sum_apply]; simp_rw [pairv (n:=n) (show Book.rank 1 (cwave n G _) from mon_leaf _) (show Book.rank 1 (cwave n G _) from mon_leaf _ )]; -- maybe gai
       simp [ cwave,onX, Landau.parity,Landau.p, lip, Motif.leaf, node1, field,cross, mul_ite, mul_add, Finset.sum_add_distrib]; rw [r_ortho k l]; ring
lemma energ (j k l: G.ColorIndex) : Mark.token (ploy G h 0) j k l = h *(Mark.LieColor j k l:ℂ) := by
   change ploy G h 0 ((onX true (none,j),0)::(onX false (none,k),0)::[(onX false (none,l),0)]) = _; rw [Captain]; simp only [phase,if_true,applyS]; rw [ plea ]; -- convert to LieColor
   have he:rune k l j=(↑(Mark.LieColor j k l):ℂ):= by rw [← r_clock j k l]; unfold rune; rw [ scaled_tensor ]
   rw [he]; ring
lemma noteX (p:SectorP n)(i:Chan G n): D (onX true i,p) (B₂ G n)=0:= by
   unfold B₂ top4; rw [map_smul]; rw [show D (onX true i,p) (∑ a:Arts.L n,∑ b:Arts.L n,sume (quill a b) (quill a b)) = (0:Rack G n) from section_sum _ (fun i _=> section_sum _ (fun j _=> ((sume_high 0 (realA i |>.jawn ( realA j ))).2.1) )) i p, smul_zero] -- maybe implicit and w unused
lemma tokenMS (j k l:G.ColorIndex) : Mark.token (pulseX G 1 0) j k l=(Mark.LieColor j k l:ℂ):= by
   rw [pulse1]; have he := congr_arg (fun T:Mob G=>Mark.token (T 0) j k l) (Class_at G 1); simp only [χ,map_add, Literal.value_sl,one_smul,one_pow] at he;
   unfold Mark.token at he; simp only [Pi.add_apply,Pi.sub_apply] at he
   have h : Mark.token (B₂ G 0) j k l=0:= congr_fun (noteX (n:=0) ( G:=G ) 0 (none,j)) [ C k 0,C l 0 ]; change (Mark.token (B₁ G 0) j k l+Mark.token (B₂ G 0) j k l)=Mark.token (ploy G 1 0) j k l- Mark.token ( ploy G 0 0 ) j k l at he; rw [energ, energ,h,add_zero] at he; simpa using he
-- the usable input
lemma allLeader (G:Gauge): ∃ X p, leader G X (gloss (pulseX G)) p:= satisfy (invest G) (funext fun _=> Up0 G)
lemma stable (hp:leader G X (gloss (pulseX G)) p): _root_.YM.MS.Wind.Compact (Archive 4 X):= by
   refine ⟨ _, Crown G,fun i j k=> tokenMS i j k, fun ⟨s,t⟩ w _ hp' => sub_eq_zero.mp ?_⟩; exact HB (r:=3) hp (invest G 1) (fun i=> (fund_one G i).up) 0 w (by omega) -- s:y
end YM.MS.Halo
