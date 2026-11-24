import YM.Qlocal.Canopy.Kelly
/-! # Upper projection (assemble thermal binding, KLIN)
 Keep at ANY order; proof extraction log from full registry & Snap. Keep prices (later) from
 support-reading coupon on each permitted p. No need smooth.Ex.Info on all unpermitted combinations,
 no pay for huge J except in algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r m:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
namespace Stellar
open Schema Canopy Canopy.Button Roller Comparison.RG02.Bulk
variable {ι:Type} [DecidableEq ι] [Fintype ι] {Z:Census ι}
variable {σ:Type} [Fintype σ] (K:σ→ reed G f) (l:σ→Multi.Hot Z)
variable (F:Forest S.ratio) (t:S.Choices) (R:Layout G)(X:Finset Age) (h:Legal X R)
    {O:ChartRatio G}{p:Clip}{P:PathData G}{a L v:ℝ}(A: Kernel S p P O) (Q:Before G a L S.patch.J S.kernel (k+3))
    (D:Bid.Dir G c→AxisChart G F)(hq: P.Bounds p a L v) (hk:Bid.Larger (G:=G) S)(hV:Q.Service F p P D) (W : Colors Z G f)
    (hw : W.vac= Binding.drawn R X f) (hK:∀ t,Flute (K t) (W.power (l t))) (he:draws K l W X R) (x:Apex c G)
local notation "R₀"=> catalogue K l F t R X h A Q D hq hk hV W hK x
abbrev script: Button.Book σ:= Function.swap R₀
local notation "RR"=>script K l F t R X h A Q D hq hk hV W hK x
local notation "Ξ"=>series Z r
local notation "Ω"=> Fk A F t W (tint G _ x) r
local notation "η"=> scribe (plant l) RR
local notation "Φ"=>sput (plant l)
local notation "G'"=>startup F O t P p Q hk hq hV A.ratio
local notation "tγ"=> Drink.sap F R X (G') h x
local notation "valley"=>realCurve Z tγ
set_option quotPrecheck false
local notation "II"=> Precision.Key F G→ℝ
local notation "s'"=> translated A F (tint G _ x)
local notation "Z'"=> Gaussian.cloud (A.covariance F t)
local notation "C"=> geometric A F t
local notation "gas"=> expansions W.power (markFn S F W) (C W)
include hw h hV hK he
local notation "shelf"=>divideTerm K l F t A Q D hq hk hV W x
lemma portrait (J:II): gas (s' J) = ∑ p:Finset σ, shelf J p:= by
 unfold expansions; let y:= (weld _).symm J; have he: markExp (curve W.power (markFn S F W) (s' J))=∑ q:Finset σ, sput (plant l) q (Roller.poem F G' (x,y) (Flute.bill K q) (Flute.size (W.power∘l) q)):= by nth_rw 1 [← show (weld _) y= J from (weld _).apply_symm_apply J]; exact seat K l F t R X h A Q D hq hk hV W hK he x y
 rw [he,Finset.mul_sum]
omit hw he
lemma penned : η=∑ P:Finset σ, Φ P (R₀ P):= (Button.swept _ _)
lemma central : Φ ∅ (R₀ ∅)=1:= by
 rw [Button.voiced]; unfold catalogue; rw [if_pos rfl]; ext1 i; rw [PowerSeries.coeff_one,realCoeff,just]; split_ifs <;> simp
lemma erase (p:Finset σ)(he:p≠∅): bottom Z r (Ξ (Φ p (R₀ p)))=0:= by
 by_cases hv:Button.Ideal l p; · rw [dyes _ hv (Finset.nonempty_iff_ne_empty.mpr he)]; exact Glyph.bare _
 rw [dies _ hv,map_zero,map_zero]
include hw he
lemma kept (J:Index r)(s:Z.Mode)(hs:s≠ Z.quiet): (Ω).part (Join.pair s J)=(Ξ (valley*η)).part (Join.pair s J):= by -- macro issue (Ω).part
 rw [Comparison.RG02.Bulk.table]; let fac:ℂ:=↑J.val.card.factorial; let A' (p) (z:II):= rows (fun z=> shelf z p) s J.val.card z; let g (z:II):= Comparison.RG02.Assembly.rows gas s J.val.card (s' z); have he z:g z=∑ i,A' i z:= by unfold g A' Comparison.RG02.Assembly.rows; rw [portrait K l F t R X h A Q D hq hk hV W hw hK he x,_root_.map_sum,Poly.part_sum]
 let u:=fun p=> quoteTerm K l F t R X h A Q D hq hk hV W hw hK x p s hs J; change fac* (∫ z,g z ∂Z')= _; simp_rw [he]; rw [integral_finsetSum, Finset.mul_sum, penned,Finset.mul_sum,_root_.map_sum,Poly.part_sum]; exact Finset.sum_congr rfl fun i hi=>(u i|>.2.symm) -- maybe rw orientation he redeclared binder local shadow
 intro p hp; exact (u p).1
lemma docked : Comparison.RG02.Order.ratio Ω= series Z r η:= by
 apply Eq.symm; refine ratio_unique (fk_unit ..) ?_; apply Eq.symm; apply Join.both_parts; intro i a; let d:= Comparison.RG02.Order.denominator Ω; have hx:d=Ξ valley:= Binding.off_axis F t R X A W h hw Q D hq hk hV x r; by_cases hr:i= Z.quiet; swap; · exact (kept K l F t R X h A Q D hq hk hV W hw hK he x a i hr).trans (by rw [map_mul,show Comparison.RG02.Order.denominator Ω =_ from hx])
 subst i; let A₀:= Join.pair Z.quiet a; have hh(b:Grade Z r): (bottom Z r b).part A₀=b.part A₀:= by rw [show A₀=_ from rfl,bottom_value,if_pos rfl] -- pattern
 have hp: bottom Z r (Ξ η)=1:= by
    rw [penned, _root_.map_sum,_root_.map_sum,sum_eq_single ∅]; rw [central,_root_.map_one,_root_.map_one];· intro i _ hi; exact erase K l F t R X h A Q D hq hk hV W hK x i hi
    simp -- indentation
 change (Ω).part A₀=(d* Ξ η).part A₀; rw [← hh _,← hh (d * Ξ η), map_mul,hp,mul_one, show d=bottom Z r Ω from rfl, bottom_repeat] -- synt (Ω).part.
omit hw he
lemma grey : Button.Grey ((Button.neutral σ) - RR):= by
 intro i; change Button.neutral σ i ∅-R₀ ∅ i=_; unfold Button.neutral catalogue just; rw [if_pos (show (∅:Finset σ)=∅ from rfl)]; split_ifs; · simp only [Merge.Switch.bench,if_true,sub_self] -- neutral formula
 exact sub_self _
include hw he
lemma breezes (hb:Fintype.card σ ≤ m) : logMarked Ω= Ξ (scribe (plant l) (Button.connect m RR)):= by
 have hz:= docked (r:=r) K l F t R X h A Q D hq hk hV W hw hK he x; unfold logMarked; rw [hz]; exact Button.logarithm _ (clicked l) (grey K l F t R X h A Q D hq hk hV W hK x) (hz ▸ (ratio_quiet (fk_unit ..))) hb
end Stellar
end YM.Qlocal.Bind
