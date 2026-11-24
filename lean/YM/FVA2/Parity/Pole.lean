import YM.FVA2.Rank.Sky
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land
/-!
# Mark parity on dimensional optics

With exactly the supplied MS (see `YM/MS` for the meaning of `Booked`).
With the slot and power-of-g conventions as in `Rank`. Gives the `sleeve`
 identity for initial marks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity
open Function Set Filter Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul MS.Heat
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Hem.Mell MS.Dock MS.Train MS.Pearl MS.Halo
open _root_.YM.MS.Shine MS.Color Garment.Wave Garment.Wick Signal Book.Convolve
open Hue MS.Emit MS.Local.Physical MS.Menus MS.Land MS.Mach MS.Motif.Literal MS.Lifting MS.Arts.Pilot
open Position Position.Glazer
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
namespace Optic
variable {G:Gauge}{n m k:ℕ}{a b:Arts.L m}{z:ℂ}
local notation "H"=>Hue.flip (Shore G m)
local notation "Ω"=>hue G
lemma eats (F V:Rack G m): H (bite m G F V)= bite m G (H F) (H V):= by
 simp_rw [← Hue.black (p:=parity)]; exact Pilot.circle_prod ..
lemma bright (F:Rack G m) : H (rowP a F)= rowP a (H F):= by funext w; simp [flip_at,rowP,moon]; ring
lemma bp (a:Arts.L m)(i:G.ColorIndex): H ( A m G a i)= - A m G a i:= by rw [ranks ( A m G a i ) (n:=1) ( mon_leaf _ ), s1,neg_one_smul ]
lemma charm (a b:Arts.L m)(i:G.ColorIndex): H (cur z a b i)= -cur (-z) a b i:= by
    let Q:= quill a b (G:=G) i; simp only [cur, Pi.add_apply,Pi.smul_apply,map_add, map_smul ]; rw [ ranks _ ( n:=1) ( rank_α _ _ _ ),ranks (jaw G m (A m G a) (A m G b) i) ( n:=2 ) ( twoQ _ _ _ ),s1,s2 0,s0,one_smul,neg_one_smul, neg_smul ]; abel
lemma pipe (a:Arts.L m)(F V: Mield G m)(h:∀ i,H ( F i )= -V i)(i:G.ColorIndex) : H ( jaw G m (A m G a) F i )= jaw G m (A m G a) V i:= by
    rw [chew,chew,map_sum]; simp_rw [map_sum,map_smul]; refine Finset.sum_congr rfl (fun i' _=> Finset.sum_congr rfl fun j _=>?_); refine congr_arg ( _ • · ) ?_; change H ( bite _ _ _ _)= bite _ _ _ _; rw [eats,bp,h,map_neg, map_neg, LinearMap.neg_apply, neg_neg]
lemma driver (a:Arts.L m)(F V: Mield G m)(h:∀ i,H ( F i )= -V i)(i:G.ColorIndex) : H (convoke z a F i)= -convoke (-z) a V i:= by
    simp only [convoke,LinearMap.add_apply, LinearMap.smul_apply, Pi.smul_apply, Pi.add_apply,map_add,map_smul, pipe a F V h i ]; unfold axisP; rw [lock,lock,bright,h,map_neg, neg_smul ]; abel
lemma poleH (a b:Axis)(l:List Axis)(i:G.ColorIndex): H (Pole G m a b z l i)=-(Pole G m a b (-z) l i):= by
    induction l generalizing i with| nil=> exact charm _ _ i| cons a l ih=> exact driver _ _ _ ih i
lemma wings (n:ℕ)(l:Fin n→Plaq)(i:Grid G n): Ω (Pole.wing n l i z)= Hue.σ n • Pole.wing n l i (-z):= by
    funext m; induction n with
    | zero=> exact ( ranks (n:=0) _ ( Rails.coin 1 ) )
    | succ n ih=>
        change Hue.flip _ (bite _ _ _ ( Pole.wing n (l∘Fin.succ) (i∘Fin.succ) z m ))=Hue.σ _ • ( bite _ _ _ _ ); rw [eats, show Hue.flip _ ( Pole_leaf (n:=m) z (l 0) (i 0) )=_ from poleH (m:=m) (l 0).i (l 0).j (l 0).jets (i 0), show Hue.flip _ ( Pole.wing n (l∘Fin.succ) (i∘Fin.succ) z m)=_ from (show Hue.flip _ _= Hue.σ n • Pole.wing n (l ∘ Fin.succ) (i ∘ Fin.succ) (-z) m from ih (l ∘ Fin.succ) (i ∘ Fin.succ)), map_smul,map_neg,LinearMap.neg_apply,ss, neg_smul,smul_neg]; rfl
lemma shown (i:ℕ)(k:ℕ)(f:ℂ→Mob G)(he:f∈ Gallery G i k) (z:ℂ) : Ω (f z)= Hue.σ i • f (-z):= by
    refine Submodule.span_induction («R»:=ℝ) (p:=fun f _=> Ω (f z)= Hue.σ i • f (-z)) ?_ ?_ ?_ ?_ he
    · rintro _ ⟨l,a,h,rfl⟩; unfold Pole.saint; simp only [map_sum,map_smul,wings,Finset.smul_sum]; exact Finset.sum_congr rfl fun j _=> smul_comm ..
    · simp only [Pi.zero_apply,map_zero,smul_zero]
    · rintro i j h k he hv; simp only [Pi.add_apply,map_add,he,hv,smul_add]
    rintro c x h hx; simp only [Pi.smul_apply,show Ω ( c • x z )= c • Ω (x z) from map_smul ((Ω).restrictScalars ℝ) c _, hx, smul_comm c (Hue.σ i)]
-- extract boxed coefficients
variable {E:Type}[AddCommGroup E][Module ℂ E]
def mutt (f:ℕ→ E→ₗ[ℂ] E) : Box E→ₗ[ℂ] Box E:= Finsupp.lsum ℂ fun i:ℕ=> ( Finsupp.lsingle i ).comp ( f i )
lemma standing (f:ℕ→ E→ₗ[ℂ] E)(V:Box E)(i:ℕ): mutt f V i= f i ( V i ):= by
    induction V using Finsupp.induction_linear with
    | zero=> rw [map_zero,Finsupp.zero_apply,map_zero]
    | add a b ha hb=> simp [ha,hb]
    | single j x=> unfold mutt; rw [Finsupp.lsum_single]; by_cases hi:i=j; subst j; simp; simp [Ne.symm hi]
lemma mul_pay (p q:ℕ)(x:Box (Mob G))(h:(fun z=> value ( Mob G ) z x)∈ Gallery G p q) (z:ℂ): value (Mob G) z (mutt (E:= Mob G) (fun i=> Hue.σ (i+p) • hue G) x )= value _ z x:= by
    let f:= mutt (E:=Mob G) (fun i=> Hue.σ (i+p) • hue G); let V:= value ( Mob G );
    have he(y:Box (Mob G)): V z (f y)= Hue.σ p • Ω (V (-z) y):= by
        induction y using Finsupp.induction_linear with
        | zero=> simp only [map_zero,smul_zero]
        | add a b ha hb=> simp only [map_add,ha,hb,smul_add]
        | single i x=> unfold f mutt; rw [Finsupp.lsum_single ]; change V z ( Finsupp.single i (Hue.σ (i+p) • Ω x) )= _; unfold V; rw [value_sl,value_sl,map_smul,Hue.sp, ← neg_one_mul z,mul_pow,smul_smul,smul_smul]; unfold Hue.σ; congr 1; ring
    rw [show value (Mob G) z _=Hue.σ p • _ from he x ]; obtain ht:= shown p q _ h (-z); rw [neg_neg] at ht; rw [ ht,smul_smul,s_id,one_smul ]
variable {Y:Deck G}{T:Booked Y}(B:MS_Data G T)(w:ℕ)(i: Plaid Y w)
lemma prepar (Y:Deck G)(T:Booked Y)(w:ℕ)(i: Plaid Y w)(k:ℕ) : Glazer.sleeve G (k+i.1.val) ( Emit.gloss (linear (Mob G) (T.optics w i)) k )=Emit.gloss (linear (Mob G) ( T.optics w i )) k:= by
    let X:=T.optics w i; let F:= mutt (fun k=> Hue.σ (k+i.1.val) • hue G); funext x; change Hue.σ (k+i.1.val) • ( Ω (X k ))= _; rw [← show (F X) k= Hue.σ (k+i.1.val) • Ω (X k)  from standing .., show F X=X from OpenAxis.ticket_eq (F X) X (mul_pay i.1.val w X ( T.law w i|>.1)) ]; rfl
end Optic
end YM.FVA2.Parity
