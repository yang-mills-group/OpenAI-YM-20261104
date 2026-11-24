import YM.MS.Milk.Bus
import YM.MS.Milk.Mural
import YM.MS.Milk.Outfit
import YM.Next.RANK.GaussTags
/-!
# Multi-standard.Even connected equation only.Expose operations.Near past estimate when all distinct, theorem.Probewise identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell Local.Physical
open Labels
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X W:Type}{G:Gauge} [LinearOrder W]{n d r:ℕ}{s:ℝ}{U:W→ℝ}{P:W→Pol G}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
open Puff SplitP Puff.Log Engine Dynamics Actors Swirl
open Puff SplitP Actors Engine Dynamics Stencil Swirl
open Land Geo Vane Osc Snap
variable {I:Type} {B:Deck G}{Mh:Booked B}{P:Geo I}{S:MS_Data G Mh} (T:W→Rake.Label B) (x:Position W I) {Y:Rake.Dance G I W} {F:Finset W}
abbrev slew (Y:Rake.Dance G I W)(i:I)(p:Finset W)(t:ℝ): Law G:= chair G (rootX x p i) (Y p 0 i t)
variable (h:Mesh P x)(he:DOrd Mh P S T x Y)(i:I)
abbrev PlainX (i:I)(w:W): E4:= fixF ( x w i )
include h
lemma PlainI : Injective (PlainX x i):= by
    intro u v hp; by_contra he; obtain ⟨A,hA,hv⟩:= ( h _ _ he|>.floor ); let y:= P.roots i; have ht:0<y:=exp_pos _; apply not_le_of_gt (mul_pos hA ht); apply ( hv i ).trans; rw [Pi.sub_apply, show x u i=x v i from fixF.injective hp,sub_self, norm_zero]
abbrev Lightning (A:Rake.Label B):= storm A.h A.item
local notation "Xκ"=> slew x Y i
set_option quotPrecheck false
local notation "Lκ" => LogU ( PlainX x i ) ( PlainI x h i ) ( Lightning ∘ T )
include he
lemma gust (hs:F.Nonempty): ∀ t,Xκ F t∈Wallet G:= by have hv:= Vane.founded ( builder S h T ) he hs 0; exact fun t=> chair_v _ ( Wallet.awake hv.2 i t )
lemma zoya (hp:F.Nonempty) : Status ( Xκ F ) ( Wrap ( Xκ F )+∑ j∈ picks F,Ink G ( Xκ j ) (Xκ (F \ j) ) ):= by
    let L:=constantP G I (PlanetD G); have hμ:= builder S h T; obtain ⟨⟨k,hk⟩,hW⟩:= Vane.founded hμ he hp 0; let u(t:Finset W):= rootX x t i; refine ⟨⟨k,fun t w hw=>?_⟩ ,fun t w=>?_⟩; · change Tone.bill _ (net w)*_= _; rw [ hk i t w hw,mul_zero ]
    obtain hm:= (Vane.motion hμ he hp 0).pace i w (fun v=>Bool.noConfusion v) t; let c:= Tone.bill (u F) (net w); convert (hm.const_mul c) using 1;
    · rfl
    · rfl
    obtain hq : ∀ j∈ picks F, Ink G ( Xκ j ) ( Xκ ( F \ j ) ) t= chair G ( u F ) ( regionC (fun _=>planeF) ( rootX x j-rootX x F ) L (Y j 0) ( Y ( F\j ) 0 ) i t ):= by
       intro j hj; have ht:u F=u ( F \j ):= congr_fun (unfT x hj) i; unfold regionC; rw [ Pi.sub_apply,congr_fun ( unfT x hj ) i,ht ]; apply ( show Ink G ( Xκ j ) ( Xκ ( F \ j ) ) t =_ from climb_c (u j) (u ( F\j )) ?_ ?_ t ); exacts [Wallet.awake ( founded hμ he (n_small hj|>.2.1) 0 ).2 i t, Wallet.awake ( founded hμ he (n_small hj|>.2.2.1) 0 ).2 i t]
    simp only [rhs,Src,multi, lonely, Domain.paths, Finset.Ico_self, Finset.sum_empty,zero_add, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Pi.add_apply,Finset.sum_apply, Finset.mul_sum, mul_add ]
    refine congr_arg₂ (· + ·) ?_ (Finset.sum_congr rfl (fun j hj=> ?_) ); · let Z:=Y F 0 i t; change deep G t ( chair G ( u F ) Z ) w= _; rw [chair_move ( u F ) ( Wallet.awake hW i t ), weightC (s:=t) (Wallet.awake hW i t) ]; rfl
    exact congr_fun (hq j hj) w
lemma sun (p:Finset W) : Xκ p=Lκ p:= by
    induction p using Finset.strongInduction with | H p ih=>
       by_cases hm:2≤p.card; swap
       · obtain hz|hn:= p.eq_empty_or_nonempty; · subst p; funext t; rw [ originL ]; simp [ slew, he.1 ]; -- rhs OM(t) equality
         obtain ⟨u,rfl⟩:= Finset.card_eq_one.mp (show p.card=1 from by have hv:= Finset.card_pos.mpr hn; omega ); funext s; unfold slew; rw [ onlyE,he.2.1 ]; change chair G _ _= arc ( storm _ _ ) ( RawS G (out ( fixF ( x u i )) ) ) _ s; rw [opening ( y:= P.η i ) ( A:= S ), LinearEquiv.apply_symm_apply ]; simp [ rootX ]; rfl -- congr
       let H:=∑ j∈ picks p, Ink G ( Lκ j ) ( Lκ (p\j)); have hs:= Finset.card_pos.mp ( show 0<p.card from (by omega) ); refine Model ( H:= H ) ?_ (Milk.motion ..) ( gust T x h he i hs ) ( fun u=> ( pureU _ _ _ p u ).1 ) atBot ( fun w=> ?_ );
       · convert! zoya T x h he i hs using 2; unfold H; apply Finset.sum_congr rfl; intro j hj; rw [ ih j ( n_small hj |>.1 ), ih ( p\ j ) (n_small hj|>.2.2.2 ) ]
       have hv : Tendsto (fun i'=>Y p 0 i i' w) atBot (𝓝 0):= by obtain ⟨_,hX,hq⟩:= he.2.2 p hm 0; rw [hq]; unfold river; exact tendsto_integral_Iic_zero tendsto_id
       simp_rw [slew, seated ]; simpa only [mul_zero,sub_zero] using ( hv.const_mul ( Tone.bill ( rootX x p i ) (net w) ) ).sub (dusk ( birthQ _ _ _ p hm w ))
end YM.MS.Milk
