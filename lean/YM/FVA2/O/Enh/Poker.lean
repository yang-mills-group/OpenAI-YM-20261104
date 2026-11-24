import YM.FVA2.O.Enh.Hold
/-!
# Uniform (in separated shape) readers for OPE matching

Projecting at input length one. `Fiasco` asks for contracting the outputs on
all compact exterior profile sets, an estimate on *ordinary* products, as the
exterior positions go far. Gap parameter b, use b = 1 for final results; k is
last output weight included; the error is coefficientwise (i < d) with
log-polynomial allowance. It does NOT assume bounded complexity as order grows.
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
variable { G: Gauge } {I J : Type}{n m d k:ℕ}
variable {s:Set ( Points n )}{S:Set ( Points m )}{u:Scan G n}{v:Scan G m}{A:Album G}{ν:ℝ}
abbrev party (A:Album G)(x:Points n)(y:Points m)(u:Scan G n)(v: Scan G m): Cn:= A _ ( forest x y ) ( Fin.append u v )
abbrev lonelyG (A: Album G)(x: Points m)(p:Q G)(v:Scan G m): Cn:= party A (0:Points 1) x ( Single p ) v
-- charge for one far projection
abbrev Settle (w:ℕ)(f:Q G→ Cn): Cn:= ∑ i:Grade G w,f (own i)
abbrev Lamp (A:Album G)(h:ℕ)(x:Points m)(v:Scan G m)(p:Q G→ Cn): Cn:= ∑ i∈Finset.range (h+1), Settle i (fun q=> p q * lonelyG A x q v)
def Basket ( A:Album G )(u:Scan G n)(v:Scan G m)(p:Q G→ Cn)(h:ℕ)(x:Points n)(y:Points m): Cn:= party A x y u v- Lamp A h y v p
abbrev Fable (G:Gauge)(n:ℕ) := Points n→ Q G→ Cn
abbrev RangeP ( A:Album G )(s: Set ( Points n ))(S:Set ( Points m ))(u:Scan G n)(v:Scan G m)(p:Fable G n)(k:ℕ)(b:ℝ)(d:ℕ): Prop:= ChargeP d ( ( k:ℝ )+b+(totalG v:ℝ) ) (fun (i:s× S) t=> Basket A u v ( p i.1.val ) k i.1.val ( squeeze (-t) i.2.val ))
abbrev Fiasco ( A: Album G )(s:Set ( Points n )) (k:ℕ)(b:ℝ)(d:ℕ)(u:Scan G n)(p:Fable G n): Prop:= ∀ m (S:Set ( Points m )) (v:Scan G m), IsCompact S→S⊆Outside m→ RangeP A s S u v p k b d
variable {O:Booked ( Press.portDeck G )} {M: MS_Data G O}
local notation "Λ"=> Counter ( Press.portDeck G )
local notation "Vμ"=> install (Equator.wave ν M)
lemma SumT (f:Q G→ Cn)(k:ℕ): ∑ i:Λ k, f ( actor i )=∑ i∈ Finset.range (k+1),Settle i f := by
    rw [ Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range ( fun i=> Settle i f ) (k+1) ]
lemma LampT (A: Album G)(h:ℕ)(x:Points m)(v:Scan G m)(p:Q G→ Cn): ∑ i:Λ h,p ( actor i ) * lonelyG A x ( actor i ) v = Lamp A h x v p:= SumT (fun i=> p i * lonelyG A x i v ) h
lemma coeffF (a b:Cn) (k:ℕ): coeff k (a*b)= ∑ j∈Finset.range (k+1), coeff j a *coeff (k-j) b:= by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=>PowerSeries.coeff i a* PowerSeries.coeff j b) ] -- name
lemma Lantern {r:Details ( Press.portDeck G ) I k}{p:I→ Q G→ Cn}(h:∀ i n v, coeff n ( p v ( actor i ) )=( r i n v: ℂ )) {x:I→ Points m} (s:Scan G m)(hv:∀ i,x i∈ Outside m)(L:Geo I)(ht:∀ i,L.η i= ν): ∀ n i, coeff n ( Lamp (Vμ) k ( x i ) s ( p i ) )= Fiscal r ( fun j=> glyph L M ( orange (fun i=> outgoing (x i)) ) ( shelf m s k j ) Finset.univ ) n i := by
    intro n i; rw [ ← LampT,map_sum,Fiscal,Finset.sum_apply,Finset.sum_apply ]; exact Finset.sum_congr rfl fun j _=> by simp_rw [coeffF,h]; exact Finset.sum_congr rfl fun u hu=> by rw [stock ν M (Fin.append _ _) (hv i),glyph,ht ]; rfl
end YM.FVA2.O.Enh
