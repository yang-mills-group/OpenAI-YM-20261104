import YM.FVA2.O.Enh.Poker
/-!
# Compact-local OPE approximation for MS (at length one)

`Locals`: for fixed order and output weight budgets choose a preliminary finite-order OPE candidate
from `O/Seam/End`. This *one* approximation prices `Fiasco`, including varying the
number of exterior insertions and the compact exterior shape set. See `O/Bind` for how
to make one choice on *all* levels from this, with the full power-log rate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Enh
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo O.Seam O.Hue
variable {G:Gauge}{ I J : Type }{ n m k d w:ℕ }
variable {O: Booked ( Press.portDeck G ) } {M:MS_Data G O} {ν:ℝ}
variable {K:Set ( Points n )}{ Y:Set ( Points m )}{u:Scan G n } {v: Scan G m } {t:ℝ}
variable (K)
abbrev ActualP (s:Set ( Points n ))(ν:ℝ): Geo (↥s):= Tide.frameF (↥s) ν
abbrev xK (K:Set ( Points n )): K→ Points n:= Subtype.val
local notation "Λ"=> Counter ( Press.portDeck G )
abbrev settle_i (i:Q G)(h:heft i ≤k): Λ k:= Dframe.enroll (G:=G) h (Land.read i.item)
lemma id_F (i: Λ k):settle_i ( actor i ) ( k:=k ) ( show heft ( actor i ) ≤ k from Dframe.size_le i )=i:=rfl
def Field_of (r:Details ( Press.portDeck G ) K k): Fable G n:= fun x i=>if h:x∈K ∧ heft i≤k then PowerSeries.mk (fun j=> ( r ( settle_i i h.2 ) j ⟨ x,h.1 ⟩:ℂ )) else 0
local notation "V"=> install ( Equator.wave ν M )
variable {K}
variable {p:Details ( Press.portDeck G ) K k}{s:Details ( Press.portDeck G ) I k}
lemma key_V (u:Λ k)(i:K)(n:ℕ): coeff n (Field_of K p i.val ( actor u ))= ( p u n i: ℂ ):= by rw [ Field_of,dif_pos (And.intro i.property ( Dframe.size_le u )), coeff_mk,id_F ]

lemma packF {r:Details ( Press.portDeck G ) I k}{f:I→ Q G→ Cn}{x:I→ Points n}{y:I→ Points m}(ht:∀ i j l,coeff l ( f i ( actor j ))= ( r j l i :ℂ )) (z:Geo I) (hp: RecipeT z M ( thicket z M ( orange x ) u Finset.univ ) k d r )(h:Cluster z (orange y) (orange x))(hv:∀ i,y i∈Outside m)(hη:∀ i,z.η i=ν)(i:ℕ)(hi:i<d)(v: Scan G m): Far_P z (totalG v+k) (fun j=> coeff i ( Basket (V) u v ( f j ) k ( x j ) ( y j ) )):= by
    let T:= Fin.append u v; let F:= orange x; let Z:= orange y; obtain hm:= hub ( x:=Z ) ( y:= F ) h ( lamp_h h ) ( greeting ( u:=v ) hv ) hp i hi; change Far_P _ _ (( glyph z M ( lamps x y ) T ( arc n m∪lit n m ) - Fiscal r (fun j=> glyph z M (orange (fun i=>outgoing ( y i ))) (shelf m v k j) ( insert (roof m) (arc 1 m) ))) i ) at hm; rw [packed,roof_lamps] at hm;
    let Y:= fun j:I=> forest ( x j ) ( y j ); obtain ha:= due ( f:=Y ) ( lamp_h ( u:=v ) ( v:=u ) h ).uses; obtain ⟨C,hC,k',h⟩:=hm; refine ⟨ C,hC,k', fun j=>?_⟩; specialize h j; dsimp only at *; -- costly? simplify chart
    rw [Basket,map_sub,Lantern ( ν:=ν ) ( M:=M ) (fun u n v=> ht v u n ) v hv z hη ]; have hr: glyph z M ( lamps x y ) T Finset.univ i j= coeff i (party (V) ( x j ) ( y j ) u v):= by rw [glyph,hη j]; exact Eq.symm ( stock ν M T ( ha j ) i )
    rw [← hr]; exact h
lemma Price_v (h:IsCompact K)(ht:K⊆conf n)(hp:RecipeT (ActualP K ν) M (thicket (ActualP K ν) M (orange (xK K)) u Finset.univ) k d p): Fiasco V K k (eps_gain/2) d u (Field_of K p):= by
    intro m S v hS hB i hi; obtain ⟨t,hH,t0⟩:= (( clusterE h ht hS hB ).and ( eventually_ge_atTop (0:ℝ) ) ).exists; let I:=Sip t K S; let L:= VenueP K S ν t t0; let ξ (i:I):= i.1.1; let x:I→Points n:= xK K∘ ξ; let y(i:I):=i.1.2.val; let z:=Stretch L y; have hM: large L x y:= hH ( P:= L ) ( fun i=> i.2.property ) x y (fun i=>i.1.1.property) ( fun i=> i.1.2.property ); have hv(i:I): z i∈Outside _:= lives (-( i.2.val )) (hB i.1.2.property);
    let f(i:I):= Field_of K p ( x i )
    have hQ: RecipeT L M ( thicket L M ( orange x ) u Finset.univ ) k d ( pullT ξ p ) := yieldQ ( P:=L ) ( M:=M ) ( Q:= ActualP K ν ) ( ξ:= ξ ) ( R:=u ) ( y:=orange (xK K) ) ( s:=Finset.univ ) ( r:=p ) (d:=d) rfl hp
    
    have hm(i:I)(j:Λ k)(l:ℕ): coeff l ( f i ( actor j ))=( pullT ξ p j l i:ℂ ):= key_V (K:=K) ( p:=p ) j (ξ i) l
    
    obtain ⟨C,hC,k',H⟩:= packF (I:= I ) ( f:=f ) ( r:=pullT ξ p ) ( x:=x ) ( y:=z ) ( u:=u ) ( M:=M ) hm L hQ hM hv ( ν:=ν ) (fun _=>rfl) i hi v; let T0:= 1+|ν|; have h0:0<T0:=by unfold T0; positivity
    refine ⟨ C*T0^k',by positivity,k',( eventually_ge_atTop t ).mono fun a ha' q=> ?_ ⟩; apply le_trans ( H (⟨ q,a,ha'⟩:I) ); unfold Need post; change C*( T0*(1+a) )^k' * Real.exp (- ((( (totalG v+k:ℕ):ℝ ))+eps_gain/2 )*a )≤ _
    rw [Nat.cast_add,mul_pow,show -( ( totalG v:ℝ )+k+eps_gain/2 ) = -( ( k:ℝ )+eps_gain/2+totalG v ) from (by abel) ]; exact le_of_eq ( by ring )
-- useful uniform boundedness
abbrev Bounded_K (f:I→ℂ): Prop:= ∃ C:ℝ,∀ i,‖f i‖ ≤ C
abbrev PlainF (s:Set ( Points n ))(f:Fable G n)(h d:ℕ): Prop:= ∀ q:Q G,heft q ≤h→∀ j<d,Bounded_K (fun x:s=> coeff j (f x q))
lemma Locals (M: MS_Data G O) (h:IsCompact K)(ht:K⊆ conf n) : ∃ f:Fable G n,Fiasco ( install (Equator.wave ν M)) K k (eps_gain/2) d u f ∧ PlainF K f k d:= by
    let L:= ActualP K ν; obtain ⟨p,hp⟩:= recipe ( M:=M ) ( P:=L ) ( Y:=u ) ( k:=k ) ( d:= d ) ( t:= Finset.univ ) (ZoneJ ( P:=L ) h ht (fun i=>(show xK K i∈K from i.property)) ) ( fixed_J h (fun i=>( show xK K i∈K from i.property)) );
    refine ⟨ Field_of K p, Price_v h ht hp,?_⟩; intro q hh i hi; let Ω:=settle_i q hh; obtain ⟨ C,hC,k',h⟩:= hp.power Ω i; refine ⟨ C*(1+|ν|)^k',fun j=>?_⟩; dsimp only; rw [ show coeff i ( Field_of K p j.val q )=_ from key_V Ω j i, Complex.norm_real ]; specialize h j; apply le_trans h; change C*((1+|ν|)*(1+ (0:ℝ)))^k' * 1 ≤ _; simp; -- maybe ambiguity and simplify
end YM.FVA2.O.Enh
