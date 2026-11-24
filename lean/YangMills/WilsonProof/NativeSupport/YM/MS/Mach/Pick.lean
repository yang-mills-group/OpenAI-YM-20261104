import YM.MS.Mach.Pick
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Mark
/-!
# D-dimensional representative freedoms.Witness represents choice independent of loops
(word basis, including relation with 4D at zero-coupling). 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Pole Local.Physical
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{k m n h d:ℕ}{b:Bool}{u:ℤ}{z:ℂ}{V: Box (Mob G)}{F H:ℂ→Mob G}{K W:Mob G}
-- Choice condition. enough to compare arbitrary F.
structure Count0 (X: Mob G) (h:ℕ)(t:ℤ): Prop where
   tab: ∀ i, Pace (X i) h t h
   civil: ShadeG X
   balloon: Sturdy false X
namespace Count0
lemma zero : Count0 (0:Mob G) h u:= ⟨fun _=>Pace.zero,fun _ _=> map_zero _,Sturdy0⟩
lemma add (h:Count0 K n u)(he: Count0 W n u): Count0 (K+W) n u:= ⟨fun i=> (h.tab i).plus (he.tab i), fun i k=> by rw [Pi.add_apply,map_add,h.civil i k, he.civil i k],Sturdy_plus h.balloon he.balloon ⟩
lemma scale (h:Count0 K n u)(x:ℝ): Count0 (x • K) n u:= ⟨fun i=>(h.tab i).cash (z:=(x:ℂ)) (by simp),fun i k=>by change repeatC k ((x:ℂ) • K i)=_; rw [map_smul,h.civil i k]; rfl,Sturdy_scale h.balloon (x:ℂ)⟩
def issueG (G:Gauge)(n:ℕ)(u:ℤ): Submodule ℝ (Mob G) where
   carrier:= setOf fun K=> Count0 K n u
   zero_mem':= Count0.zero
   add_mem' := Count0.add
   smul_mem' c _x h:= Count0.scale h c
end Count0
structure Gnome (F:ℂ→Mob G)(k h:ℕ): Prop where
    real' (z:ℝ): Count0 (F z) h 0
    rank0 n: Book.rank k (F 0 n)
    good (p:ℂ)(i:ℕ): Safe (F p i) p
    consistent (p:ℂ): ShadeG (F p)
namespace Gnome
lemma zero : Gnome (0:ℂ→Mob G) k h:= ⟨ fun _=> Count0.zero,fun _=> Rails.zero, fun _ _=>Safe.zero, fun _ _ _=>map_zero _⟩
lemma add (hx:Gnome F k h)(ht:Gnome H k h) : Gnome (F+H) k h:= ⟨ fun z=> (hx.real' z).add (ht.real' z),fun i=> (hx.rank0 i).add (ht.rank0 i),fun k i=> (hx.good k i).add (ht.good k i),fun i n g=>by simp only [Pi.add_apply,map_add,hx.consistent i n g,ht.consistent i n g]⟩ -- g variable ok
lemma pose (hx: Gnome F k h)(c:ℝ): Gnome (c • F) k h:= ⟨fun z=> (hx.real' z).scale c,fun i=> ( hx.rank0 i).smul (c:ℂ),fun i j=> (hx.good i j).cashR c,fun i n g=>by change repeatC g ((c:ℂ) • F i n)=_; rw [map_smul,hx.consistent i n g]; rfl⟩
lemma saint_ok (k:ℕ)(f:Fin k→Plaq)(i:Grid G k): Gnome (saint k f i) k (wage k f):= ⟨ fun z=> ⟨fun _=> Pole.reality k f i (by simp), angel k f i, apric k f i⟩, fun _=> Pole.fare k f i,fun _ _=> real_h k f i,fun _=> angel k f i⟩ -- ambig `angel`
lemma GalleryG (H:F ∈ Gallery G n h): Gnome F n h:= by
   refine Submodule.span_induction (p:=fun F _=> Gnome F n h) ?_ zero (fun _ _ _ _=>add) (fun c _f _ hf=>hf.pose c) H; rintro f ⟨a,x,rfl,rfl⟩; exact saint_ok n _ _
end Gnome
lemma onZero (x:Box (Mob G)): linear (Mob G) x 0=value (Mob G) 0 x := (low_row x).symm
namespace Ele
variable {A:Law G} (he:Ele h k A V)
include he
lemma grows : Schema false 0 h (Emit.gloss (linear (Mob G) V)):= by intro n; have ht: Count0 (V n) h 0:= Present.pay (f:=fun z=>value (Mob G) z V) (K:= Count0.issueG G h 0 ) (show ∀ i:ℝ, value _ i V ∈ Count0.issueG G h 0 from (Gnome.GalleryG he.1).real') V (fun _=>rfl) n; exact Pace.prepay ht.tab ht.balloon ht.civil
lemma moodQ : Emit.Trill (pulseX G) (linear (Mob G) V):= by let P:= Gnome.GalleryG he.1; apply judgment ( fun i m=> (P.good i m).sym ); exact fun z=>funext fun i=> tail_shutdown ( P.good z i ) ( P.consistent z i )
lemma Top : Goods k (linear (Mob G) V 0):= by rw [onZero]; exact (Gnome.GalleryG he.1).rank0
end Ele
lemma pin {W:Law G}(H:W∈ Allowed G h k): ∃ V,Ele h k W V := by
   refine Submodule.span_induction (p:=fun W _=>∃ V,Ele h k W V) ?_ ?_ ?_ ?_ ( syntaxK H )
   · rintro A ⟨a,σ,hq,H0,rfl⟩; obtain ⟨V,hV⟩:= presence k a σ; refine ⟨ V,?_,?_⟩; · rw [hV]; exact Submodule.subset_span (s:=Sentence G k h) ( Set.mem_setOf.mpr ⟨ a,σ, Nat.cast_injective (R:=ℤ) (( Pole.payZ k a).trans hq), rfl ⟩)
     rw [← low_row V, show value (Mob G) 0 V=saint k a σ 0 from congr_fun hV 0]; exact y_floor k a σ
   · refine ⟨0,?_,rfl⟩; simp only [map_zero]; exact Submodule.zero_mem _
   · rintro f g _ _ ⟨V,hV,h⟩ ⟨A,hA,h'⟩; refine ⟨V+A, (show (fun z=>_)∈ Gallery G k _ from ?_), ?_⟩; simp_rw [map_add]; exact Submodule.add_mem _ hV hA; rw [Finsupp.add_apply,Pi.add_apply, h,h']
   rintro c f H ⟨V,hV,hw⟩; refine ⟨c • V,?_,?_⟩; simp_rw [lng]; exact Submodule.smul_mem _ _ hV; rw [Finsupp.smul_apply,Pi.smul_apply, hw]
open Menus Train Pearl
variable {B:Deck G} {p q: T (Coat G)}{X Y:T ( Flats G )} {j:Glyph B d}
lemma initialHF (h:Ele d j.grade j.read V)(hx:j.size=d)(hv: comet d 0 X (Emit.gloss (linear (Mob G) V)) Y q): _root_.YM.MS.Wind.Leading.PhysicalHF j (Archive d Y):= by
   let F:= linear ( Mob G ) V; let A:=F 0 0; have he : A=j.read:= h.2; have hp:= Ele.Top h 0
   have ht: Limit A j.grade:= fun w hw=> hp w (by rw [mod_int]; omega);
   have hV(y t:ℝ) : Limit (( Archive d Y 0 (y,t) )-A) (j.grade-2):= (HM hv (h.grows 0) (s:=t) (y:=y) (r:=j.grade) (fun n l hl=> Ele.Top h n l (by rw [mod_int]; omega))) 0
   refine ⟨ hx, fun ⟨y,t⟩=>?_ ,fun ⟨y,t⟩=>?_ ⟩; · rw [← sub_add_cancel ( Archive d Y 0 (y,t) ) A]; exact ((hV y t).up (by omega)).add ht
   rw [← sub_add_cancel (Archive d Y 0 (y,t)) A, map_add, Menus.maskOff (by omega) (hV y t),zero_add, (show mask (j.grade:ℤ) A=A from rank_hat _ |>.mp hp),he] -- budget name conflict.
end YM.MS.Mach
