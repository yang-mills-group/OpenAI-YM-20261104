import YM.FVA2.O.Read.Homes
/-!
# Exact $B_T(I)$ and smeared limit on joint inner shapes

Definition at all T; if far-family has not attained noncollision on all positions covered
by the tests, unimportant value chosen by the defaulted integral. No OPE assertion about such
collisions. Rates uniform in fixed compact (other file); here compute the limiting kxcoeff.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable { G: Gauge }{I:Type}{ n m d i k:ℕ}{ A:Album G }{ H:ℝ→Frames G}{V:Arenas G}{P:Geology G d}{ r:ℝ→Cn }
variable {u:Scan G n}{ x:Points n }{ q: Test n }{ a v t:ℝ}{ s:Set (Points n) }{f:Fable G n}
local notation "V'"=> install V
abbrev Dock (H:ℝ→ Frames G)(A:Album G)(P:Geology G d)(u:Scan G n)(t:ℝ)(q: Test n)(b: Toon G d):= smearing q (fun x=> Perch H A P u t x b)
abbrev FProg (H:ℝ→ Frames G)(A:Album G)(P:Geology G d)(u:Scan G n)(t:ℝ)(q: Test n): Toon G d→ Cn:= ( ( Sheet H A P t )⁻¹ ) *ᵥ Dock H A P u t q
abbrev FromK (p:Fable G n)(t: Test n)(b:Toon G d):= smearing t (fun x=> p x ( flash b ))
lemma allows_q (h:Part t s P)(he:IsCompact s)(ht:Observed A)(p: Toon G d)(k:ℕ): ContinuousOn ( fun x=> coeff k ( QuoteShape H A P u t x p ) ) s:= by
    unfold QuoteShape Matrix.mulVec dotProduct; apply sum_on; intro j _ i; exact stableV ( A₁:=fun (_:Points n)=> (( Sheet H A P t )⁻¹) p j ) ( fun _=> continuousOn_const ) ( fun i=> look ( H:=H ) he h ht i j ) i
lemma price_g (h:Part t ( CoverP q ) P)(he:Observed A)(b: Toon G d): FProg H A P u t q b= smearing q (fun x=> QuoteShape H A P u t x b ):= by
    unfold FProg QuoteShape Matrix.mulVec dotProduct; rw [ smearing_sum ]; · exact Finset.sum_congr rfl (fun j _=> ( smearing_mul q ( fun i=> look ( H:=H ) ( u:=u ) q.hasCompactSupport h he i j ) _ ).symm )
    intro j _; exact region _ ( fun i=> look q.hasCompactSupport h he i j ) _
variable (h:Law V r H)(hp: Regular V)(he:Observed (install V))( ht:Detected V P)
include h hp he ht
lemma growth_v (hK:Fiasco V' ( CoverP q ) d v k u f)(hP:PaceX f)(b:Toon G d): ChargeP k ((d:ℝ)+v-( heft ( flash b ):ℝ) ) ( fun (_:I) t=> FProg H V' P u t q b- FromK f q b ):= by
    let K:= CoverP q; have hC: K⊆ conf n:= q.tsupport_subset; have h' : IsCompact K:= q.hasCompactSupport; obtain hT:= post_quote h hp he h' hC ht hK b; let A (x:Points n)(t:ℝ):= QuoteShape H V' P u t x b; let V := V; let R:= fun x=> f x ( flash b ); let F (x:Points n)(t:ℝ):= A x t-R x; have hL:= life P h' hC;
    have hh : draw q R:= fun i=> ( hP _ i ).mono hC; have hg(t:ℝ)(hv:Part t K P): draw q (fun x=> A x t) := fun i=> allows_q hv h' he b i; have H0 : ∀ᶠ t:ℝ in atTop, draw q ( fun x=> F x t ) := hL.mono fun t ht i=> (by unfold F; simp_rw [map_sub]; exact ( hg t ht i ).sub ( hh i ) )
    intro i hi; refine Rain.raise ( paid_u ( I:=I ) ( f:=F ) hT H0 i hi ) ( hL.mono ?_ ); intro t ht _; unfold FromK; dsimp only; rw [ price_g ht he ]; unfold F; rw [ smearing_sub q ( hg t ht ) hh ]
lemma limit_κ (hF:AllC V' u f)(v:Test n)(b:Toon G d)(i:ℕ): Tendsto (fun t=> coeff i ( FProg H V' P u t v b )) atTop (𝓝 ( coeff i ( FromK f v b ) ) ) := by
    obtain hp := growth_v ( q:=v ) ( I:=Unit ) h hp he ht ( hF.2.2 ( CoverP v ) v.hasCompactSupport v.tsupport_subset d ( i+1 ) ) hF.2.1 b i ( Nat.lt_succ_self i ); have ht : ( heft ( flash b ):ℝ ) ≤ ( d:ℝ ):= (by exact_mod_cast size_le b); obtain hc:= ( Rain.lapse hp ( by linarith ) ).tendsto_at (); simp_rw [ map_sub ] at hc; have hT:= Filter.Tendsto.add_const ( coeff i ( FromK f v b ) ) hc; simpa only [ Pi.zero_apply,sub_add_cancel, zero_add ] using hT -- type
end YM.FVA2.O.Read
