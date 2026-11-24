import YM.FVA2.O.Read.Homes
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
/-!
 # formal mark-raising operator on the chosen graded alphabet

 Use all real tangent slots. One-step differential at fixed arbitrary order;
 assigned raising in engineering dimensions by exactly one. The matrix may
 involve all field rows in that grade (including the case of empty output rank);
 convolution with its higher-order coefficients is appropriate at nonzero order.
 -/
variable {G:Gauge}{W E :Type}{a n m k:ℕ}
open Smooth
abbrev Staff (G:Gauge):= ∀ (P: Q G), Axis→ Grade G (heft P+1)→ Cn
def Raise (A:Staff G)(i:Fin n)(v:Axis)(p:Scan G n): ( Scan G n→ Cn )→ₗ[Cn] Cn where
    toFun F:= ∑ j, A (p i) v j * F ( Function.update p i ( own j ) )
    map_add' f g:= by simp only [Pi.add_apply,mul_add, Finset.sum_add_distrib ]
    map_smul' a f:= by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm ( A _ _ _ ) a, Finset.mul_sum ]; -- maybe
variable (A:Staff G) (i:Fin n)(v:Axis)(p:Scan G n) (F F':Points n→ Scan G n → Cn) (k:ℕ)
def spot (i:Fin n)(v:Axis) : Points n →L[ℝ] ℝ:=
    ContinuousLinearMap.proj v ∘L ( Theater.out.toContinuousLinearEquiv.toContinuousLinearMap ∘L ( PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin n=> E4) i ) )
def italy (i:Fin n)(v:Axis): ℂ→L[ℝ] (Points n →L[ℝ] ℂ):= ContinuousLinearMap.smulRightL ℝ _ _ (spot i v)
lemma appears (y:ℂ)(x:Points n): italy i v y x= ( x i v ) • y:= rfl
-- jet pob.Y.Declare Destiny.
abbrev Γ (Q:Staff G)(F:Scan G n→Cn)(p:Scan G n)(k:ℕ) : Points n→L[ℝ]ℂ:= ∑ i:Fin n,∑ v: Axis, italy i v (coeff k (Raise Q i v p F))
-- maybe conflict glyphs. support statement
abbrev Shard (Q:Staff G)(F:Points n→ Scan G n→Cn)(x:Points n): Prop:= ∀ i k, HasFDerivAt (fun x=> coeff k ( F x i )) ( DerivD.Γ Q (F x) i k ) x
def Influence (Q:Staff G)(J: Album G):Prop:= ∀ n:ℕ,∀ x∈conf n, Shard Q (J n) x
variable (x:Points n)
lemma Rise_add (X Y:Scan G n→ Cn): DerivD.Γ A ( X+Y ) p k= DerivD.Γ A X p k+DerivD.Γ A Y p k:= by simp_rw [DerivD.Γ,map_add,Finset.sum_add_distrib]
lemma Rise_sub (X Y:Scan G n→ Cn): DerivD.Γ A ( X-Y ) p k= DerivD.Γ A X p k-DerivD.Γ A Y p k:= by simp only [DerivD.Γ,map_sub,Finset.sum_sub_distrib]
lemma Rise_sum (F:W→ Scan G n→ Cn)(s:Finset W): DerivD.Γ A (∑ i∈s,F i) p k=∑ i∈s,DerivD.Γ A (F i) p k:= by
    simp_rw [DerivD.Γ,map_sum]; rw [Finset.sum_comm (s:=s)]; exact Finset.sum_congr rfl fun i _=> Finset.sum_comm ..
lemma priceF (Y:Scan G n→ Cn)(d:Cn): DerivD.Γ A (d • Y) p k = ∑ j∈ Finset.range (k+1), ( coeff j d ) • DerivD.Γ A Y p (k-j):= by
    unfold DerivD.Γ; ext1 x; simp_rw [ _root_.sum_apply, _root_.smul_apply,_root_.map_smul,smul_eq_mul, coeffF,appears ]; -- RHS .apply
    simp_rw [_root_.sum_apply,appears,Complex.real_smul, Finset.mul_sum]; rw [Finset.sum_comm (s:= Finset.range (k+1))]; refine Finset.sum_congr rfl fun x hx=>?_ ; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> mul_left_comm ..
variable {A F F' p k x}
namespace Shard
lemma along (h:Shard A F x)(d:Cn): Shard A (fun i=> d • F i) x:= by
    intro v k; rw [ priceF ]; simp_rw [ Pi.smul_apply, smul_eq_mul, coeffF ]; exact HasFDerivAt.fun_sum ( fun i _=> ( h v (k-i) ).const_mul _ ) -- check
lemma plus (h:Shard A F x)(ht:Shard A F' x): Shard A ( F + F' ) x:= by intro v k; simp_rw [Pi.add_apply, map_add, Rise_add ]; exact ( h v k ).add ( ht v k )
lemma sub (h:Shard A F x)(ht:Shard A F' x): Shard A ( F - F' ) x:= by intro v k; simp_rw [Pi.sub_apply,map_sub, Rise_sub ]; exact ( h v k ).sub ( ht v k )
lemma league (s:Finset W)(F:W→Points n→ Scan G n→ Cn)(h:∀ i∈s, Shard A (F i) x): Shard A (fun x u=>∑ i∈s,F i x u ) x:= by intro b k; simp_rw [map_sum]; rw [show (fun u:Scan G n=>∑ i∈s,F i x u )= ∑ i∈s,F i x from (by funext y; rw [Finset.sum_apply]), Rise_sum]; exact HasFDerivAt.fun_sum fun i hi=> h i hi b k
end Shard
