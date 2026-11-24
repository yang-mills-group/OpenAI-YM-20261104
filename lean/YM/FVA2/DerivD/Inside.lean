import YM.FVA2.DerivD.Plant
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
# Push the first position derivative through smearing profiles

This is on formal continuum kernels only. Applications via FAR probes at
fixed separated positions: `DerivD/Rite`.
-/
open O.Read
variable {G:Gauge}{n m k:ℕ}{E:Type*}{T K:Set (Points n)}{p:Test m}{a:Staff G}
variable {F:Points n→ Points m → Scan G n→ Cn}{v:Scan G n}{x:Points n}
variable (q:Scan G n)
local notation "Λ"=>volume.restrict (CoverP p)
private lemma moors [NormedAddCommGroup E][NormedSpace ℝ E]{g:Points n→Points m→E}(hp:ContinuousOn (uncurry g) (K×ˢ CoverP p))(ht:x∈K): Integrable ( g x ) Λ:= ( show ContinuousOn (g x) ( CoverP p ) from hp.comp (f:=fun i=> (x,i)) ( Continuous.prodMk continuous_const ( continuous_id ( X:=Points m ) ) ).continuousOn ( fun _ hp=> ⟨ht,hp⟩ ) ).integrableOn_compact p.hasCompactSupport
private lemma cutS {g:Points m→ℂ}: p.applyTo g= ∫ y,p y * g y ∂Λ:= by
    rw [ Test.applyTo,← treasury p, integral_indicator (isClosed_tsupport _).measurableSet, treasury p ]
variable (hP:∀ i:Scan G n, O.Read.draw_s (fun x y=> F x y i) p K)
include hP
-- gamma expectation from integrand lifted marks.
lemma contV (i:Fin n)(v:Axis)(k:ℕ)(a:Staff G): ContinuousOn (fun t:Points n× Points m=> coeff k ( Raise a i v q ( F t.1 t.2 ) )) ( K×ˢ CoverP p ):= by
    unfold Raise; simp_rw [LinearMap.coe_mk, AddHom.coe_mk,map_sum, coeffF ]; exact continuousOn_finsetSum _ fun j _=> continuousOn_finsetSum _ fun t _=> continuousOn_const.mul (hP _ _)
-- for $italy` ∑. commuting multiplying by p exterior test coefficient. Need Lean complex linear?
lemma γthm (x:Points n)(hx:x∈K)(q:Scan G n)(i:Fin n)(j:Axis)(a:Staff G)(k:ℕ): coeff k ( Raise a i j q ( fun u=> smearing p ( fun y=> F x y u )))= ∫ y, p y * coeff k ( Raise a i j q ( F x y )) ∂Λ:= by
    unfold Raise; rw [ ← cutS (p:=p) ]; simp_rw [LinearMap.coe_mk, AddHom.coe_mk];
    rw [ ← show coeff k ( smearing p (fun y=> ∑ j':Grade G ( heft ( q i )+1 ), a _ j j'* F x y ( update q i ( own j') )) )= _ from coeff_mk k _ ]; -- hope elaborator. maybe wrong direction
    rw [smearing_sum]; · congr 1; exact Finset.sum_congr rfl fun j _=> ( smearing_mul p ( draw_once (hP _) hx ) _ ).symm
    intro i _; exact region _ ( draw_once ( hP _ ) hx ) _
lemma gammaA (q:Scan G n)(x:Points n)(hx:x∈K): DerivD.Γ a (fun i=> smearing p (fun y=> F x y i)) q k= ∫ y, p y • DerivD.Γ a (F x y) q k ∂Λ:= by
    let S:= CoverP p; let g(i:Fin n)(v:Axis)(y:Points m):= p y * coeff k ( Raise a i v q ( F x y ) ); have hh(i v): Integrable (g i v) Λ:= by
        apply moors (g:= fun x y=> p y* coeff k ( Raise a i v q ( F x y ) )) _ hx; exact (p.continuous.comp continuous_snd).continuousOn.mul (contV q hP i v k a)
    have he (i:Fin n)(v:Axis)(k m:ℂ): k • (italy i v m)=italy i v ( k*m ):= by ext1 p; simp only [appears,_root_.smul_apply,smul_eq_mul,Complex.real_smul]; ring
    have hg(i v) : Integrable (fun y=> italy ( n:=n ) i v (g i v y)) Λ:= (italy i v).integrable_comp ( hh i v ); unfold DerivD.Γ; simp_rw [ Finset.smul_sum, he ]; change _=∫ y,∑ i:Fin n,∑ v:Axis, italy i v (g i v y) ∂Λ; rw [ integral_finsetSum _ ( fun i _=> integrable_finsetSum _ fun j _=> hg i j ) ]; refine Finset.sum_congr rfl fun i he=>?_ ; rw [ integral_finsetSum _ ( fun j _=>hg i j ) ]; apply Finset.sum_congr rfl; intro j hi; rw [ γthm hP x hx q i j ]; exact ( (italy i j).integral_comp_comm ( φ:=g i j ) (hh i j) ).symm
lemma Shard.profiles (hx:IsCompact K)(ht: x∈ interior K)(he:∀ x∈ interior K,∀ t∈ CoverP p, Shard a ( fun u i=> F u t i ) x): Shard a ( fun v i=> smearing p (fun y=>F v y i) ) x:= by
    intro q i; let S:= K ×ˢ ( CoverP p ); let P:= volume.restrict ( CoverP p ); let g (x:Points n)(t:Points m):= p t * coeff i ( F x t q ); let T (x:Points n)(t:Points m):= p t • DerivD.Γ a (F x t) q i; have hg : ContinuousOn ( Function.uncurry g ) S:= (p.continuous.comp continuous_snd).continuousOn.mul ( hP _ i ); have hT : ContinuousOn ( Function.uncurry T ) S:= by
        apply (p.continuous.comp continuous_snd).continuousOn.smul; exact continuousOn_finsetSum _ fun v _=> continuousOn_finsetSum _ fun j _=> (italy v j).continuous.comp_continuousOn ( contV q hP v j i a )
    let heq := ( isClosed_tsupport ( show Points m→ℂ from p ) ).measurableSet; letI : IsFiniteMeasure P:= ⟨ by unfold P; rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact p.hasCompactSupport.measure_lt_top ⟩;
    obtain ⟨C,hC⟩ := IsCompact.exists_bound_of_continuousOn ( hx.prod p.hasCompactSupport ) hT; have hh:= isOpen_interior.mem_nhds ht;
    have hp : ∀ᵐ x ∂P,x∈ CoverP p:= ae_restrict_mem heq; have h0 := hasFDerivAt_integral_of_dominated_of_fderiv_le ( F:=g ) ( μ:=P ) ( F':=T ) hh ( Filter.eventually_of_mem hh ( fun x hx=> ( moors hg ( interior_subset hx ) ).1 ) ) ( moors hg ( interior_subset ht ) ) ( moors hT ( interior_subset ht ) ).1 ( hp.mono fun y hy x hx=> hC ( x,y ) ⟨ interior_subset hx,hy ⟩ ) ( integrable_const C ) ( hp.mono fun y hy z hz=> ( he z hz y hy q i ).const_mul _ ); simp_rw [ gammaA hP q x (interior_subset ht), smearing, coeff_mk, cutS ]; exact h0
end YM.FVA2.DerivD
