import YM.FVA2.O.Project.Beacon
/-!
# Polynomial in the logarithm of the inverse separation radius

Preservation of powers-of-log form and log-polynomial costs, at each chosen order.
`QuoteP` has a further **power** of the scale; this is about log pricing, see `Beacon`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Project
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind
variable {G:Gauge}{ I J: Type }{n m d k:ℕ }{a b:ℝ }{ p q:Cn }
variable { T U:ℝ→ Cast G }{r:ℝ→ Cn}{ u w:Scan G n }{ v:Scan G m }{s:Set ( Points n )}
variable { A:Album G }
abbrev BLog (G:Gauge)(n:ℕ):= Scan G n→ FLog G n
abbrev ledger (r:ℝ→ Cn)(T U:ℝ→ Cast G)(f:BLog G n): BLog G n:= fun u t x=> refund ( T t ) ( U t ) ( r t ) ( fun i=> f i t x ) u
variable { f:BLog G n }{g:FLog G n}
lemma certify (h:Pace.formal ( f:=fun (_:Unit) t=> r t )): Pace.formal (fun (_:I) t=> r t):= by
    intro k; obtain ⟨d,hD⟩:= h k; exact ⟨ d,fun _=> hD () ⟩
lemma price_cs (h:Town U)(i j:Grade G d): Pace.formal (fun (_:I) t=> U t d i j) := certify (fun k=>Rhythm.unit.mp ( h d i j k ))
lemma pace_sum {f:I→ J→ℝ→Cn}(s:Finset I)(h:∀ i∈s,Pace.formal ( f i )): Pace.formal ( fun i t=>∑ j∈s, f j i t ):= by
    intro i; simp_rw [map_sum]; exact Pace.sum s fun j hj=>h j hj i
lemma price_path (h:Town T)(u:Scan G m)(x:LivesP u): Pace.formal (fun (_:I) t=> play ( T t ) u ( decode u x )):= by
    unfold play decode; simp_rw [ report ]; exact Pace.formal.prod _ ( fun j _=> price_cs h _ _ )
lemma price_tag (h:Town T)(ξ:Scan G m)(B:I→ℝ→ Scan G m→ Cn)(he:∀ x:LivesP ξ,Pace.formal ( fun i t=> B i t ( decode ξ x ) )): Pace.formal ( fun i t=> concert ( T t ) ξ ( B i t ) ):= by unfold concert; exact pace_sum _ ( fun j _=> Pace.formal.mul ( price_path ( I:=I ) h _ _ ) ( he j ))
lemma cost_tag (h:Town T)(ξ:Scan G m)(B:I→ℝ→ Scan G m→ Cn)(he:∀ x:LivesP ξ, ChargeP d a ( fun i t=> B i t ( decode ξ x ))): ChargeP d a ( fun i t=> concert ( T t ) ξ ( B i t ) ):= ChargeP.sum _ (fun j _=> ChargeP.times ( ChargeP.extreme h _ _ ) ( he j ))
lemma pay_CS (h:Town U)(i j:Grade G d): ChargeP k 0 ( fun (_:I) t=> U t d i j ):= fun k _=> Rain.rhythm ( h d i j k )
lemma continual_k {A:I→ Cn}[TopologicalSpace I] {s:Set I}(hx:∀ i,ContinuousOn (fun j=> coeff i ( A j )) s)(h:Rooted p)(k:ℕ): ContinuousOn ( fun x=> coeff k ( ( A x ).subst p )) s := by
    simp_rw [← Constants.actual_subst _ _ h, coeff_mk,rules,smul_eq_mul ]; exact continuousOn_finsetSum _ ( fun i _=> ( hx i ).const_mul _ )
variable {A₁ B:I→ Cn}
lemma stableV {s:Set I} [TopologicalSpace I](h:∀ i,ContinuousOn (fun x=> PowerSeries.coeff i ( A₁ x )) s)(he:∀ i,ContinuousOn (fun x=> PowerSeries.coeff i ( B x )) s)(k:ℕ): ContinuousOn (fun i=> PowerSeries.coeff k ( A₁ i * B i )) s:= by
    simp_rw [ coeffF ]; exact continuousOn_finsetSum _ (fun i _=> (h i).mul ( he _ ))
lemma sum_on {s:Set I} [TopologicalSpace I]( B:J→ I→ Cn )(p:Finset J)(h: ∀ j∈p, ∀ k:ℕ,ContinuousOn ( fun i=> coeff k ( B j i ) ) s)(k:ℕ): ContinuousOn ( fun i=> coeff k (∑ j∈p,B j i) ) s:= by simp_rw [map_sum]; exact continuousOn_finsetSum _ (fun i hi=> h i hi k )
lemma credit_fore (B:Cast G)(q:Cn)(F:Scan G n→ Fable G n)(h:∀ i,PaceX ( F i ))(hp:Rooted q)(v:Scan G n): PaceX (fun x=> credit B q ( fun i=> F i x ) v ):= by
    intro b k; unfold credit concert; refine sum_on ( fun (j:LivesP v) x=> _ ) _ ?_ k; intro i _ k; refine stableV ( A₁:=fun (_:Points n)=> play B v ( decode v i )) ( fun _=>continuousOn_const ) ?_ k; exact continual_k ( A:=fun x=> F ( decode v i ) x b ) ( fun _=> h _ _ _ ) hp
lemma receipt_fore (B:Cast G)(f:Fable G n)(h:PaceX f): PaceX ( fun x=> receipt B ( f x ) ):= by
    intro b k; unfold receipt; refine sum_on (fun (i:Grade G (heft b)) x=>f x (own i)* B _ i b.item ) _ ?_ k; intro i _ t; exact stableV ( A₁:=fun x=> f x (own i) ) ( B:=fun _ :Points n=> B _ i b.item ) ( fun j=> h _ j ) ( fun _=> continuousOn_const ) t
variable (hv:∀ i:Scan G n,Markup ( f i ))(h:Town T)(he:Town U)(hp:Meter.Clear r)(hq:∀ t,Rooted (r t))
local notation "V"=> ledger r T U f
include hv h he hp hq
lemma price_turn (v:Q G): Pace.formal ( fun x t=> V u t x v ) := by
    unfold ledger refund credit receipt; refine pace_sum _ ( fun i _=> Pace.formal.mul ( price_tag h u _ (fun j=>?_ ) ) ( price_cs he _ _ ) ); exact Pace.formal.substitute ( (hv _).poly _ ) ( certify hp ) ( fun _ t=> hq t )
lemma pay_turn (hT:IsCompact s)(hV:s⊆conf n)(b:Q G): ChargeP d 0 ( fun (x:↥s) t=> V u t x.val b ):= by
    unfold ledger refund credit receipt; refine ChargeP.sum _ ( fun i _=> ChargeP.times ( cost_tag h u _ ( fun j=>?_ )) ( pay_CS he _ _ ) ); exact ChargeP.Pact (( hv _ ).clocks s hT hV _ _ ) ( ChargeP.clean hp ) ( fun _ t=> hq t )
omit h he hp
lemma pay_W (t:ℝ): PaceX ( V u t ):= by
    obtain hF:= credit_fore ( T t ) ( r t ) (fun i=> f i t) ( fun i=> (hv i).stays t ) ( hq t ) u; exact receipt_fore _ _ hF
lemma marked_0 (t:ℝ): Off ( V u t ):= by
    intro i hi; funext q; unfold ledger refund receipt credit concert; simp only [ Markup.off ( hv _ ) t i hi, Pi.zero_apply, ← coe_substAlgHom (Reg.Choice.licence _ ( hq t )), map_zero,mul_zero, Finset.sum_const_zero,zero_mul ] -- simp binder hv_
include h he hp
lemma markup : Markup (V u):= ⟨ price_turn hv h he hp hq, marked_0 ( T:=T ) ( U:=U ) hv hq, pay_W ( T:=T ) (U:=U) hv hq, fun _ ht H b _=> pay_turn hv h he hp hq ht H b ⟩
-- single fixed town.System.
omit hv h he hp hq
abbrev Club ( f: Scan G n→ Fable G n ) : BLog G n:= fun u _=> f u
lemma calm (g:Scan G n→ Fable G n)(h: ∀ i,AllC A i (g i)): Markup (Club g u):= ⟨ fun _=> Pace.formal.fixed _,fun _=> ( h u ).1, fun _=>(h u).2.1, fun _ ht H p _ _ hi=> Rain.cash ( Bind.philosophy ( h u|>.2.1 ) ht H ( k:=heft p ) p le_rfl _ hi ) ⟩
end YM.FVA2.O.Project
