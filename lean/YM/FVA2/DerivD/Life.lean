import YM.FVA2.DerivD.Harmonic
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
# Continuum derivative law on the entire position family

`Shard`: constant (moment-dependent) coefficients, at most one more field
weight. `Legible` for smoothness. `lending` and `NormP` for working in the
same frames under scale transformations.
-/
variable {G:Gauge}{n m k:ℕ}{x:Points n}{A:Staff G}
variable {F: Points n→ Scan G n → Cn }
abbrev Rows (G:Gauge)(n:ℕ):= Scan G n × ℕ
def Living (A:Staff G)(n:ℕ)(i:Rows G n)(f: Rows G n→ℂ): Points n →L[ℝ]ℂ:= DerivD.Γ A (fun p:Scan G n=> PowerSeries.mk (fun k=> f (p,k) )) i.1 i.2
lemma sigil (u:Scan G n→Cn)(p:Scan G n)(k:ℕ): Living A n ( p,k ) (fun i=> coeff i.2 (u i.1))= DerivD.Γ A u p k:= by unfold Living; refine congr_arg (fun x=>DerivD.Γ A x p k) (funext fun u=>?_); exact PowerSeries.ext fun i=> PowerSeries.coeff_mk ..
lemma inhabits (A:Staff G)(n:ℕ)(q:Rows G n): Stencil ( Living A n q ):= by
    unfold Living DerivD.Γ; unfold Raise; simp_rw [LinearMap.coe_mk, AddHom.coe_mk,map_sum,coeffF,coeff_mk ] -- simp_rw map_sum expands italy over ? integr
    -- trace
    apply Stencil.cap; intro a _; apply Stencil.cap; intro b _; apply Stencil.cap; intro c _; simp_rw [map_sum]; apply Stencil.cap; intro i hi; exact Stencil.only (italy a b ∘L (ContinuousLinearMap.mul ℝ ℂ ((coeff i) ( A _ _ c )) )) _
lemma Legible {s:Set ( Points n )}(ho:IsOpen s)(he:∀ i∈s, Shard A F i)(i: Scan G n)(k:ℕ): ContDiffOn ℝ ∞ ( fun x=> coeff k ( F x i )) s := by
    let f(j:Rows G n)(x:Points n):= coeff j.2 ( F x j.1 ); exact contDiffOn_infty.mpr ( fun m=> chainM ( A:=Living A n ) ( f:=f ) ho (fun j x hx=> ( he x hx j.1 j.2 ).congr_fderiv ( sigil (F x) j.1 j.2 ).symm ) ( inhabits A n ) m ( i,k ) )
private lemma owe (i:Fin n)(p:Scan G n)(v:Q G): totalG (update p i v)+heft (p i)=totalG p+heft v:= by
    unfold totalG; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ (fun i=> heft (p i)) ( Finset.mem_univ i ) ]; -- arguments
    simp_rw [ update_self ]; rw [ Finset.sum_congr (s₂:=( Finset.univ.erase i )) ( g:=fun i=> heft (p i) ) rfl (fun i hi=> by rw [update_of_ne (Finset.mem_erase.mp hi).1] ) ]; omega -- names
lemma owe_m (i:Fin n)(p:Scan G n)(v:Grade G (heft (p i)+1)): totalG (update p i (own v))=totalG p+1:= by obtain he:= owe i p ( own v ); rw [ show heft ( own v )= heft (p i)+1 from rfl ] at he; omega -- goal
abbrev lending (n:ℕ)(t:ℝ): Points n→L[ℝ] Points n:= (Real.exp (-t)) • ContinuousLinearMap.id ℝ _
def NormP (t:ℝ)(F:Points n→ Scan G n→Cn) (x:Points n)(p:Scan G n): Cn:= Acres t ( totalG p ) * F ( squeeze t x ) p
lemma raisedPay (A:Staff G)(t:ℝ)(F:Scan G n→Cn)(x:Points n)(p:Scan G n)(k:ℕ): Γ A (fun v=> Acres t (totalG v)* F v) p k x = O.Score.fee t ( totalG p ) * Γ A F p k ( squeeze t x ):= by
    unfold Γ Raise Acres; simp_rw [ _root_.sum_apply, appears, LinearMap.coe_mk, AddHom.coe_mk, owe_m, mul_left_comm ( A _ _ _ ) (PowerSeries.C (O.Score.fee t _)), ← Finset.mul_sum, coeff_C_mul ]; -- struggle
    simp_rw [ Finset.mul_sum,O.Score.fee,squeeze,PiLp.smul_apply,smul_eq_mul,Complex.real_smul ]; push_cast; simp only [mul_add,Complex.exp_add]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; ring_nf
lemma normed (t:ℝ)(h: Shard A F ( squeeze t x )): Shard A ( NormP t F ) x:= by
    intro u n; unfold NormP Acres; simp_rw [ coeff_C_mul ]; refine ( ( ( h u n ).comp x ( ( lending _ t ).hasFDerivAt ) ).const_mul _ ).congr_fderiv ?_; ext1 q; exact ( raisedPay A t _ q u n ).symm
end YM.FVA2.DerivD
