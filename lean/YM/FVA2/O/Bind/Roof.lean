import YM.FVA2.O.Bind.Baskets
/-!
# FAR detection at a specified output weight and perturbative order

`sparse`: the part of the far projection to peel away, either lower weight or lower order of
coefficient. See `sampled` for remaining far projection on tests from `O/Enh/Care`
(`nail` along the time axis).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Bind
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh
variable { G:Gauge }{n m k i d : ℕ }{v:ℝ }{ V:Arenas G }{B:ℝ→Frames G}{R:ℝ→Cn}{A:Album G}
variable {s:Set ( Points n )}{K:Set ( Points m )}{y:Points m}{x:Points n}{f g:Fable G n}{a:Scan G n}{u:Scan G m}
local notation "A0"=> install V
def sparse (A:Album G)(f:Fable G n)(k:ℕ)(x:Points n)(y:Points m)(u:Scan G m)(i:ℕ): ℂ:=
    ( coeff i ( ∑ j∈ Finset.range k, wage j A y u ( f x ) ) )+ ∑ j:Grade G k, ∑ t∈ Finset.range i, coeff t ( f x ( own j ) )*coeff (i-t) ( lonelyG A y ( own j ) u )
abbrev finPath (x:Points n)(f:Fable G n)(k:ℕ)(i:ℕ)(b:Grade G k): ℂ:= coeff i ( f x ( own b ) )
def sample (A:Album G)(f:Fable G n)(a:Scan G n)(b:Toon G k)(x:Points n)(t:ℝ)(i:ℕ): ℂ :=
    let y:= squeeze (-t) RootG; let u:= Single ( flash b ); coeff i ( party A x y a u )- sparse A f k x y u i
lemma earn (u:Scan G m): coeff i ( Lamp A k y u ( f x ))= sparse A f k x y u i+∑ j:Grade G k, finPath x f k i j * coeff 0 ( lonelyG A y ( own j ) u ):= by
    unfold Lamp; rw [ Finset.sum_range_succ,map_add ]; unfold sparse; rw [add_assoc]; refine congr_arg₂ (·+·) rfl ?_ ; unfold Settle; rw [map_sum, ← Finset.sum_add_distrib ]; apply Finset.sum_congr rfl; intro j _; rw [coeffF, Finset.sum_range_succ,Nat.sub_self ]
abbrev read_n (V:Arenas G)(f:Fable G n)(x:Points n)(i k:ℕ)(b:Toon G k):ℂ:= Enh.detect V k ( finPath x f k i ) b
abbrev wght (b:Toon G k): ℕ:= totalG ( Single ( Dframe.flash b ) )+ k
lemma flashBack (h:Law V R B)(t:ℝ)(b:Toon G k)(j:Grade G k): coeff 0 ( lonelyG A0 ( squeeze (-t) RootG ) ( own j ) ( Single (Dframe.flash b) ) )= Score.fee t (wght b)* NOW A0 b j:= by
    let X:= Fin.append ( Single ( Score.own j ) ) ( Single ( Dframe.flash b ) ); have hx : totalG X=wght b:= by unfold X; rw [totalW,totalOne]; exact add_comm ..
    change coeff 0 ( A0 _ ( outgoing _ ) X)=_; rw [← squeeze_home (-t), Enh.Uniform.lead_k h, neg_neg,hx ]
lemma anticipate (h:Law V R B)(f:Fable G n)(b:Toon G k)(a:Scan G n)(t:ℝ)(x:Points n)(i:ℕ): sample A0 f a b x t i = Score.fee t (wght b)*read_n V f x i _ b + coeff i ( Basket A0 a ( Single ( flash b ) ) ( f x ) k x ( squeeze (-t) RootG ) ) := by
    unfold sample Basket; rw [map_sub,earn]; unfold read_n Enh.detect; simp only [ LinearMap.coe_mk, AddHom.coe_mk ]; simp_rw [ Finset.mul_sum, flashBack h, mul_left_comm ( Score.fee t ( wght b ) ) ]; abel
lemma sampled (h:Law V R B)(b:Toon G k) (hF:Fiasco A0 s k v d a f)(hi:i<d): Rain v ( fun (x:↥s) t=> Score.fee (-t) ( wght b )*sample A0 f a b x.val t i-read_n V f x.val i k b ):= by
    obtain he:= hF 1 {RootG} (Single ( flash b )) (isCompact_singleton) ( singleton_subset_iff.mpr ok_wall ) i hi; obtain he : Rain ((k:ℝ)+v+(totalG (Single ( flash b )):ℝ)) _ := he.pull (fun i:↥s=> ( i,(⟨ RootG,mem_singleton _⟩: ({ RootG }: Set ( Points 1 ))) )); simp_rw [ anticipate h f,mul_add,← mul_assoc (Score.fee (-_) _), show ∀ (t d:ℝ), Score.fee (-t) d*Score.fee t d = 1 from fun t d=> (mul_comm _ _).trans (fee_mul ..), one_mul, add_sub_cancel_left ]; apply Rain.size ( Rain.mul ( a:=-(wght b:ℝ) ) _ he ); · push_cast [wght]; linarith
    exact ( show Rain ( -( wght b:ℝ ) ) (fun (_:s) t=>Score.fee (-t) ( wght b )) from (by simp_rw [ show ∀ t:ℝ,Score.fee (-t) (wght b)=_ from fun t=>(by simp only [Score.fee, neg_mul_neg,neg_neg] : Score.fee (-t) (wght b)=Score.fee t (- ( wght b:ℝ))) ]; exact Rain.all_fee ) )
end YM.FVA2.O.Bind
