import YM.MS.Milk.Basil
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
variable {A X W:Type}{G:Gauge} [DecidableEq W]{n d r:ℕ}{s:ℝ}{U:W→ℝ}{P:W→Pol G}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
variable (x:W→ E4)(hp:Injective x)
abbrev Many (W:Type)(G:Gauge):= W × Key G
def Forum (G:Gauge)(x:W→E4): Album (Many W G) G where
    H i:= ( RawS G (out ( x i.1 )) ).H i.2
    cost i:= ( RawS G (out (x i.1)) ).cost i.2
    line i:= ( RawS G (out (x i.1)) ).line i.2
abbrev eitherX (i j:Many W G): ℂ:= if i.1=j.1 then 0 else legKernel (slope i.2) (slope j.2) (x i.1-x j.1) -- branches actual coerces?
def entry (G:Gauge)(x:W→ E4)(hp:Injective x): Normal.Symmetric (Many W G):={
   cov i j:= eitherX x i j
   symm i j:= by unfold eitherX; by_cases hs:i.1=j.1; · rw [if_pos hs, if_pos hs.symm ];
                 rw [if_neg hs,if_neg (Ne.symm hs), ← neg_sub ( x i.1 ) ( x j.1 ) ]; obtain ht:= Maxwell.exchange ( slope i.2 ) ( slope j.2 ) ( show _∈ Maxwell.away from ( sub_ne_zero.mpr (hp.ne hs ) )); -- fix var
                 -- parse
                 exact congr_arg (fun t:ℝ=>(t:ℂ)) ht}
def Taxi (G:Gauge)(x:W→ E4)(hp:Injective x)(s:ℝ): Normal.Symmetric (Many W G):={
    cov i j:= eitherX x i j-pastK i.2 j.2 (x i.1-x j.1) s
    symm i j:= congr_arg₂ (· - ·) ((entry G x hp).symm i j) (by rw [ ← star_k i.2 j.2, neg_sub ]) }
local notation "Fκ" => Forum G x
local notation "Tκ" => Taxi G x hp
lemma stayT : Standard Fκ Tκ:= by
    constructor; intro i j s; have ht:= (ClockCert i.2 j.2).speak (x i.1) (x j.1) s;
    obtain hv:= ( ( ht.neg ).const_add ( eitherX x i j )); rw [neg_neg] at hv; apply (show HasDerivAt _ _ _ from ?_); simp_rw [Taxi, sub_eq_add_neg ]; exact hv
lemma pure_b (i:W)(p:Pol G): bowl Fκ (Normal.post i p)= bowl ( RawS G ( out ( x i ) ) ) p:= by
    induction p using MvPolynomial.induction_on with | C a=> rw [post_C,t_C,t_C]| add p q hp hx=> rw [ map_add,map_add,map_add,hp,hx]| mul_X p j he=> rw [map_mul,t_M,t_M,he,post_X,t_X,t_X]; rfl
lemma standardμ (P:W→Pol G)(i:W) (s:ℝ): arc (Normal.post i ( P i )) Fκ Tκ s = arc ( P i ) ( RawS G ( out ( x i ) ) ) ( Bend G ) s:= by
    let L:= out ( x i ); let f (k:Key G):Many W G:= (i,k); have hv : Normal.scope (fun k=> Finsupp.single (f k) 1) ( Tκ s )= Bend G s:= by apply Normal.Symmetric.ext; funext k j; rw [match_name f]; unfold Taxi Bend; simp only [f,eitherX,↓reduceIte,sub_self,zero_sub]; -- maybe `$s` anchor.
    unfold arc Tint; simp only [LinearMap.comp_apply]; unfold Normal.post; rw [ ← show ((fun k => ((i,k):Many W G))) = f from rfl ] at hv; rw [ labelled, Normal.prepared, hv, ← labelled, ← (show ∀ p:Pol G,Normal.post i p=MvPolynomial.rename f p from fun _=>rfl),pure_b ]
omit hp
local notation "Mκ" => fun (s:ℝ)=> Normal.self ( fun (_:W)=> Bend G s )
lemma zero_field (v:W): True:= trivial
lemma solo_H (u:W)(b:Finset W)(F:W→Pol G)(h:u∉b)(s:ℝ): arc (pot (insert u b) F) Fκ Mκ s=arc (F u) ( RawS G (out (x u)) ) (Bend G) s ⋆ arc (pot b F) Fκ Mκ s:= by
    let T:= Mκ; have he (Q:Finset W): milk (T s) (pot Q F)=pot Q (fun i=> milk ( Bend G s ) ( F i )) := shelter _ (fun i a b=> if_pos rfl ) (fun _ _ h i j=> if_neg h ) _ _; unfold arc Tint; change bowl Fκ ( milk (T s) ( pot _ _ ) ) = _ ⋆ bowl Fκ ( milk (T s) ( pot _ _ )); rw [ he,he,pot,pot, Finset.prod_insert h,t_M,pure_b ]; rfl -- syntax `Mκ` lambda parenth.Check
include hp
lemma economics : giantΦ Tκ∧ giantΦ Mκ∧ cleanΦ Tκ Mκ:= by
    have he (i j:Key G)(x:E4): Tall0 (fun y=> -pastK i j x y):= ((ClockCert i j).up x).imp fun z hz=> hz.neg_left -- name. incl economical.
    refine ⟨ fun i j=> ?_,(fun i j=> ?_),fun i j=>?_⟩
    · unfold Taxi; simp_rw [sub_eq_add_neg]; exact sunny0 ( tallC (eitherX x i j) ) ( he i.2 j.2 (x i.1-x j.1) )
    · unfold Normal.self; simp only; split_ifs; exact he _ _ _; exact tallC 0
    unfold Taxi Normal.self Bend eitherX; by_cases h:i.1=j.1; · simp only [h, ↓reduceIte, sub_self,zero_sub ]; exact fun i=> shorn0 _
    simp only [h, ↓reduceIte, sub_zero ]; simp_rw [ ← neg_sub (pastK i.2 j.2 (x i.1-x j.1) _)  ]; -- orientation? neg_sub a b =-(a-b) = b-a
    exact fun p=> ( (ClockCert i.2 j.2 ).fees ( x i.1-x j.1 ) ( sub_ne_zero.mpr (hp.ne h) ) p ).neg_left
-- far and log.ABC
lemma near_home (p: Normal.poly (Many W G)): Clean ( arc p Fκ Tκ- arc p Fκ Mκ ):= summitμ (economics x hp).1 (economics x hp).2.1 (economics x hp).2.2 p
end YM.MS.Milk
