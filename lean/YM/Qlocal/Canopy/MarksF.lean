import YM.Qlocal.Canopy.Roller
import YM.Qlocal.Canopy.Deline
import YM.Qlocal.Curtain
/-!
 # Multi-Fk.Exponent tape for arbitrary analytic input LOG registry.
 Occupations of each vertex supported individually; t^q pole relative to its ENTIRE exponent,
 arbitrary collision geometry. Only working in fixed orientation with fired vacuum kernel here;
 it certifies ALL forests later in actual theory.
 Establish before resetting coupling & vacuum scalar. Keep independent mark endpoints.
-/
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
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
namespace Stellar
open Schema Canopy Canopy.Button Roller Comparison.RG02.Bulk
variable {ι:Type} [DecidableEq ι] [Fintype ι] {Z:Census ι}
variable {σ:Type} [Fintype σ] (K:σ→ reed G f) (l:σ→Multi.Hot Z)
variable (F:Forest S.ratio) (t:S.Choices) (R:Layout G)(X:Finset Age) (h:Legal X R)
    {O:ChartRatio G}{p:Clip}{P:PathData G}{a L v:ℝ}(A: Kernel S p P O) (Q:Before G a L S.patch.J S.kernel (k+3))
    (D:Bid.Dir G c→AxisChart G F)(hq: P.Bounds p a L v) (hk:Bid.Larger (G:=G) S)(hV:Q.Service F p P D) (W : Colors Z G f)
    (hw : W.vac= Binding.drawn R X f) (hK:∀ t,Flute (K t) (W.power (l t)))
-- compatibility input: actual marker immersion. independent binding vs Pose normalization.
local notation "W'[" i "]"=>Glyph.solo (l i) (K i) R X (W.power (l i))
-- Avoid requiring filler.W.vac from Flute solo when decomposing at arbitrary x.
def draws (X:Finset Age)(R:Layout G): Prop:= W.mark= ∑ i:σ, (Glyph.solo (l i) (K i) R X (W.power (l i))).mark
variable (he:draws K l W X R)
local notation "C"=> markFn S F
-- syntax issues.local.W.θ ghost.
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "E"=> Comparison.RG02.Bulk.Joint S F
local notation "s'"=> translated A F
local notation "G'"=>startup F O t P p Q hk hq hV A.ratio
local notation "Γ"=> weld (Precision.Key F G)
local notation "Ω"=> Comparison.RG02.Assembly.curve
include hV hK h
variable (x:Apex c G)
local notation "κ'"=> s' (tint G _ x)
local notation "L'[" i "]"=> Roller.poem F G' (x,i)
local notation "wire"=> Glyph.wire
abbrev screen (i:σ)(y:Y):= Glyph.wire (l i) (Roller.poem F (startup F O t P p Q hk hq hV A.ratio) (x,y) (K i) (W.power (l i)))
local notation "H'"=>screen K l F t A Q D hq hk hV W x
include he
lemma stars (y:Y): Ω W.power (markFn S F W) (κ' (Γ y))=∑ i:σ, screen K l F t A Q D hq hk hV W x i y:= by
 let u (i:σ):= W'[i]; let z:= κ' (Γ y); let V:=Ω W.power (C W); let Ψ (i:σ):= Ω (u i).power (C (u i));
 have hx : ∀ i:σ, H' i y= Ψ i z:= fun i=> Eq.symm (Schema.mark_chart _ F t R X _ h (hK i) A Q D hq hk hV x y); simp_rw [hx];
 ext1 i; rw [map_sum]; ext v
 by_cases hh:v=Z.quiet; · rw [hh,mark_curve_quiet,Poly.part_sum]; exact Eq.symm (Finset.sum_eq_zero (fun i _=> mark_curve_quiet ..))
 let b: Multi.Hot Z:= ⟨v,(Comparison.RG02.Cumulants.hot_iff_ne v).2 hh⟩
 have hb (W:Colors Z G f) : ((PowerSeries.coeff i) (Ω W.power (C W) z)).part v= markLetter W.power (C W) b z i:= by unfold Comparison.RG02.Assembly.curve; rw [PowerSeries.coeff_mk]; exact part_lit _ b
 let f (i:σ):= C (u i) b
 have hr t: (C W b) t= ∑ i,f i t:= by
    unfold markFn posed; rw [he]; dsimp [f]; simp_rw [Finset.sum_apply]; rfl
 have hy (i:σ) : ContDiffAt ℝ ω (f i) 0:= (Comparison.RG02.Bulk.joint_receipt S F ((Glyph.approved _ (K i) R X h (hK i)).1.suppose_mark b)).smooth
 have hb' i' : ((PowerSeries.coeff i) (Ψ i' z)).part v=Comparison.RG02.Assembly.jet (f i') (W.power b + i) z:=by
   unfold Ψ; rw [hb]; by_cases h:b=l i'; · unfold f; rw [h]; rfl
   have h': f i'= fun _=>0:= by ext1 x0; dsimp only [f,markFn,posed,u,Glyph.solo]; rw [if_neg h]
   unfold markLetter; change Comparison.RG02.Assembly.jet (f i') _ z= _; rw [h']; simp [Comparison.RG02.Assembly.jet]
 change ((PowerSeries.coeff i) (Ω W.power (C W) z)).part v=_; rw [hb,Poly.part_sum]; simp_rw [hb']; rw [markLetter,Comparison.RG02.Assembly.jet,show markFn S F W b=_ from funext hr, iteratedFDeriv_fun_sum_apply (fun i hi=> (hy i).of_le le_top)]; simp only [Comparison.RG02.Assembly.jet,ContinuousMultilinearMap.sum_apply, Finset.smul_sum] -- Maybe coeff clm
-- mark exp product conversion. all cards & shutters; equality of formal series (NOT norm). 
section products
omit hV he hK h
variable {y:σ→Word ℝ}
private lemma spool₀ (v:Finset σ): Poly.pass (∑ i∈v,series Z r (wire (l i) (y i)))= ∏ i∈v,(series Z r (wire (l i) (y i))+1):= by
 induction v using Finset.induction_on with
 | empty=>rw [sum_empty,Finset.prod_empty, Extra.Trajectories.pass_zero]
 | insert i s hi ih=>
     rw [sum_insert hi,prod_insert hi,Extra.Trajectories.pass_add,Glyph.passive, add_comm 1, ih]; · exact Glyph.monochrome _
     rw [Poly.part_sum]; exact Finset.sum_eq_zero fun _ _=> Glyph.monochrome _
private lemma spool (v:Finset σ): series Z r (markExp (∑ i∈v, wire (l i) (y i)))= series Z r (∑ p∈v.powerset,∏ i∈p,wire (l i) (y i)):= by rw [← prod_add_one, map_prod, mark_exp, map_sum, spool₀]; simp_rw [map_add,map_one]; intro n; rw [map_sum, Poly.part_sum]; exact Finset.sum_eq_zero fun i hi=> by rw [Glyph.wired,if_neg (Glyph.never (l i)|>.symm)]
lemma spoolP (v:Finset σ): markExp (∑ i∈v, wire (l i) (y i))= ∑ p∈v.powerset,∏ i∈p,wire (l i) (y i):= by ext1 i; exact (observation _ _ _ (show i ≤ i from le_rfl)).symm.trans (Eq.trans (congr_arg (fun x=> observe _ _ x i) (spool l v)) (observation Z i _ le_rfl))
end products
lemma seat (y:Y): let q:= W.power ∘ l; Comparison.RG02.Assembly.markExp (Ω W.power (C W) (κ' (Γ y)))= ∑ p:Finset σ, sput (plant l) p (L'[y] (Flute.bill K p) (Flute.size q p)):= by
 intro k; rw [stars K l F t R X h A Q D hq hk hV W hK he x]; change markExp (∑ i:σ,wire (l i) (L'[y] (K i) (k i)))=_; rw [spoolP]; change ∑ p∈_, _= _; refine Finset.sum_congr (by ext; simp) fun p hp=> Roller.forest F K k (G') (x,y) (fun i _=>hK i) l -- parser arrow shape
end Stellar
end YM.Qlocal.Bind
