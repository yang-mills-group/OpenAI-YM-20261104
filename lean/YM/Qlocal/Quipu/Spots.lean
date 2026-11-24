import YM.Qlocal.Quipu.Brew
import YM.Qlocal.Quipu.Needle
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c f:Side} {S:StepData c f}{d t a v u C:ℝ}{R:Census V}
open Album Blaze
abbrev assign (S:StepData c f) (u:V→Site S.ratio.count)(o:V→Site c):= fun i:V=> S.ratio.assemble (o i,u i)
namespace Tale
open Lagger Binding Turbin Primitives.TwoWave Primitives.TwoWave.RealSlice AllOrder.Ker
variable (F:Forest S.ratio) (T:S.Choices) {b:Clip} {P:PathData G}{O:ChartRatio G} (W:Layout G)(T₀:Finset Age)
local notation "E"=> Apex c G
local notation "I"=> Leaf c V
local notation "Z"=> Precision.Key F G
local notation "Y"=> Poll.Body Z
local notation "L"=>E × rule V c
local notation "D"=>fieldDir G c 1
variable (U : Tale R G) (X: Tale.Decision U) {σ G' θ :ℝ} (A:Before G σ G' S.patch.J S.kernel (j+3))(ρ:fieldDir G c 1→ AxisChart G F) (h : Legal T₀ W) (K : Kernel S b P O)
variable (o:V→Site c) (φ:V→Site S.ratio.count)
local notation "Z'"=> U.mood X (assign S φ o) W T₀
local notation "M"=> viewed R o
set_option quotPrecheck false
abbrev lag (U:Tale R G) := fun v:V => U.power v+1
local notation "W'"=> U.lag
private abbrev sent {E₀ F σ:Type}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup E₀][NormedSpace ℝ E₀][NormedAddCommGroup σ][NormedSpace ℝ σ]: ((E₀×F)×σ)→L[ℝ]E₀×σ := ((ContinuousLinearMap.fst ℝ E₀ F).comp (ContinuousLinearMap.fst ℝ (E₀×F) σ)).prod (ContinuousLinearMap.snd ℝ (E₀×F) σ)
private abbrev slotB {F E₀ σ:Type}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup E₀][NormedSpace ℝ E₀][NormedAddCommGroup σ][NormedSpace ℝ σ]: ((E₀×F)×σ)→L[ℝ]F := (ContinuousLinearMap.snd ℝ E₀ F).comp (ContinuousLinearMap.fst ℝ (E₀×F) σ)
variable [Fintype V]
local notation "Ξ"=> orbit (G:=G) F ρ
local notation "ψ"=> colorful (fderiv ℝ (Ξ) 0)
variable (s:Senses R)(t:Places s c)
lemma hence : (dues (lag U) s.val) = boom U s+(essence s).card:= by unfold boom lag dues; rw [sum_add_distrib, sum_const,smul_eq_mul,mul_one]; rfl
include U in
lemma flow : 0< (dues (lag U) s.val):= by rw [hence]; have hv:= Finset.card_pos.mpr s.property; unfold essence; omega
-- R.k orientation root pad $. lesson positive marker assets.Ink regeneration.Peak ∀ q before ess Blossom.
def life (k:ℕ)(u:(Apex c G × rule V c) × Poll.Body (Precision.Key F G)) := if dues (lag U) s.val ≤ k then
     let f:= U.markℓ X (assign S φ (Sonnet.fill s t)) s
     Radial.jet (posed S F f) (k-(essence s).card) (Binding.gaugeL F (colorful (fderiv ℝ (orbit (G:=G) F ρ) 0) ((sent) u))) * placard t u.1.2 else 0
abbrev activity (k:ℕ) := ∑ s: Senses R,∑ t:Places s c, life F U X ρ φ s t k
variable (x:Apex c G)(y:Poll.Body (Precision.Key F G))
set_option quotPrecheck false
local notation "L'"=>activity F U X ρ φ
local notation "Y'"=> life F U X ρ φ
open AllOrder.Fire
set_option maxHeartbeats 320000 in
private lemma bench (w:ℝ → Config G f→ℝ)(j:ℕ) : Rank ((Apex c G×rule V c) × Poll.Body (Precision.Key F G)) (j+(essence s).card) (fun x=> Radial.jet (posed S F w) j (Binding.gaugeL F (ψ (sent x))) * placard t x.1.2):= by
 let g:=posed S F w; let b:= fderiv ℝ (Ξ) 0; let L₀:= softPlane b; let V':= Binding.gaugeL (G:=G) F; have he:Rank _ (j) (Radial.jet g (j)):= (Rank.hom (ContinuousLinearMap.id ℝ _) (iteratedFDeriv ℝ (j) g 0)).scal _
 let f' (x:E×Y):= Radial.jet g (j) (V' (colorful b x)); have hh:Rank (E × Y) (j) f':= by
     have hp(x:E × Y):colorful b x=((1:ℝ),0)+L₀ x:=by unfold colorful L₀ softPlane; simp -- ok
     simp_rw [f',hp]; exact Rank.app (Rank.lead he V'.toContinuousLinearMap) L₀.toContinuousLinearMap _
 --
 exact (hh.lead (sent (F:=rule V c))).mul ((product_rank t).lead (slotB (F:= (Leaf c V→ℝ)) (E₀:=Apex c G) (σ:=Poll.Body (Precision.Key F G)))) -- try.E
set_option maxHeartbeats 160000 in
lemma life_rank : ∀ i:ℕ, Rank ((Apex c G × rule V c) × Poll.Body (Precision.Key F G)) i (life F U X ρ φ s t i):= by
 intro i; by_cases hx:(dues (lag U) s.val) ≤ i; swap; · rw [show Y' s t i=(fun _=>0) from funext fun x=> if_neg hx]; exact Rank.nil i 0
 apply Rank.up (n:=i-(essence s).card+(essence s).card); swap; · rw [hence] at hx; omega
 unfold life; simp_rw [if_pos hx]; exact bench ..
lemma licensed (i:ℕ): Rank ((Apex c G × rule V c) × Poll.Body (Precision.Key F G)) i (L' i):= Rank.sum fun t _=> Rank.sum fun i _=>life_rank ..
lemma starts : L' 0=0:= Finset.sum_eq_zero fun t ht=> Finset.sum_eq_zero fun i _=> funext fun x=> if_neg (flow U t|>.not_ge)
omit [Fintype V] in
lemma ancestral (o v: V→Site f)(h: ∀ i∈ essence s,o i=v i): markℓ U X o s=markℓ U X v s:= by
  have ht(j e n): Bay.Hears (U.array s e n j).stage o ↔ Bay.Hears (U.array s e n j).stage v:= by
     unfold Bay.Hears; apply forall_congr'; intro i; apply forall_congr'; intro hl; rw [h _ hl,h _ (ownership s)]
  unfold markℓ playing Album.picture; simp_rw [ht,h _ (ownership s)]
local notation "ν"=> translated K F (tint G _ x)
variable (hL : P.Bounds b σ G' θ)(hk:Bid.Larger (G:=G) S)(he:A.Service F b P ρ) (hp:U.Allows a C)(ha:0<a)
local notation "Φ"=> ContinuousLinearMap.inr ℝ (Apex c G) (rule V c)
local notation "G'"=> Wall.pole Φ Y
local notation "t₀"=> ((x,(0:rule V c)),y)
local notation "λ₀"=> Wall.polar G' t₀
local notation "U'"=>U.markℓ X (assign S φ o)
set_option maxHeartbeats 480000 in
lemma label (i:ℕ) : wall (M) (λ₀ (∑ t:Places s c,life F U X ρ φ s t i))= if dues (lag U) s.val ≤ i then ((Radial.jet (posed S F (U' s)) (i-(essence s).card) ((Binding.gaugeL F) (ψ (x,y)))) • Poly.send s.val 1) else 0:= by
 by_cases h:(dues (lag U) s.val) ≤  i; swap
 · rw [Finset.sum_eq_zero (f:=fun t=> life F U X ρ φ s t i) (fun t _=> funext fun x=> if_neg h),if_neg h]; exact (sky_c (M) 0).trans (map_zero _)
 rw [if_pos h, Wall.finite_path, pours _ _ _ (fun i _=> Wall.granted _ _ _ (life_rank ..|>.read))]; let g(p:V→Site f): ℝ:= Radial.jet (posed S F (U.markℓ X p s)) (i-(essence s).card) (Binding.gaugeL F (ψ (x,y)))
 have he(t: Places s c): λ₀ (life F U X ρ φ s t i)=g (assign S φ (Sonnet.fill s t)) • placard t:= by
   unfold Wall.polar life g; simp_rw [if_pos h]; ext1 z; simp [sent,Wall.pole] -- edit
 rw [Finset.sum_eq_single (selected s o)];
 · rw [he, pours_s _ (product_rank _|>.read),owns,if_pos rfl]; refine congrArg (· • Poly.send s.val 1) ?_; unfold g; rw [ancestral U X s (assign S φ (Sonnet.fill s (selected s o))) (assign S φ o) (fun i hi=>congrArg (fun z:Site c=> S.ratio.assemble (z,φ i)) (filled_here o i hi))] -- order args
 · intro t ht hx; rw [he,pours_s _ (product_rank _|>.read), owns,if_neg hx.symm,smul_zero]
 simp
end Tale
end YM.Qlocal.Quipu.Sonnet
