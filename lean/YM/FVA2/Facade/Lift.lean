import YM.FormalOPE.RG10.Sync.Bills
/-!
# Core quadratic square -- native RG10's OFF-truss unmasked system

Kept all indices, including on every internal row, when freezing a FULL free coarse
field. This module just does the Gaussian splicing at an arbitrary joint. The norm
convention is deliberately irrelevant here (finite rank real), as is the normalization
of the ambient Lebesgue volume; contrast Haar jets on orbit links. We maintain as exact
PowerSeries (over polynomial functions); no independent choices of estimates through
order `p`. This will let us expose the conditional transfer of the same system in
several formulations.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter MeasureTheory PertExtension Precision Lattice GaussianScore
open MultiGauge Splice Papers Quadratic MultiGauge.Stack MarkovChain
open scoped Classical Topology BigOperators ContDiff ENNReal
variable {E F B Y K:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup B][NormedSpace ℝ B]
 [NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup K][NormedSpace ℝ K]

lemma decided (a:Quadratic E) (h:a.RespectsPrice): h.inner.P=a.P:= h.choose_spec.symm
lemma definite (a:Quadratic E) (h:a.RespectsPrice)(x:E)(hx:x≠0): 0<a.flourish x:= by
 unfold flourish; rw [←decided a h]; obtain ⟨c,hc,H⟩:= h.inner.slope; specialize H x; have he:0<h.inner.P x x/2 := (mul_pos hc (pow_pos (norm_pos_iff.mpr hx) 2)).trans_le H; linarith
lemma positiveProduct (a:Law E)(b:Law F): (addOn (drag (LinearMap.fst ℝ E F) (recordQ a)) (drag (LinearMap.snd ℝ E F) (recordQ b))).RespectsPrice:= by
 let f:= addOn (drag (LinearMap.fst ℝ E F) (recordQ a)) (drag (LinearMap.snd ℝ E F) (recordQ b)); refine ⟨⟨f.P,f.side,?_, (a.smooth.comp continuous_fst).add (b.smooth.comp continuous_snd)⟩,rfl⟩
 obtain ⟨c,hc,H⟩:= a.slope; obtain ⟨d,hd,G⟩:= b.slope
 refine ⟨min c d,lt_min hc hd,fun (x,y)=> ?_⟩
 rw [Prod.norm_def]; change min c d * (max ‖x‖ ‖y‖)^2 ≤ (a.P x x+b.P y y)/2
 rw [add_div]; rcases le_total ‖x‖ ‖y‖ with hl|hl
 · rw [max_eq_right hl]; apply le_trans (b:=b.P y y/2) _ (le_add_of_nonneg_left ((mul_nonneg hc.le (sq_nonneg _)).trans (H x))); exact (mul_le_mul_of_nonneg_right (min_le_right ..) (sq_nonneg _)).trans (G _)
 rw [max_eq_left hl]; apply le_trans (b:=a.P x x/2) _ (le_add_of_nonneg_right ((mul_nonneg hd.le (sq_nonneg _)).trans (G y))); exact (mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _)).trans (H _)
-- square in OpenSlots variables needn't have Hessians on all-coarse
lemma square_snd [FiniteDimensional ℝ E] (q:Quadratic (E×F))(hq:(core q).RespectsPrice)(y:F)(x:E): q.P (skew q hq y,y) (x,0)=0:= by
 rw [show (skew q hq y,y)=(skew q hq y,0)+(0,y) by simp,map_add,LinearMap.add_apply]; change (core q).P (-(hq.inner.inverse (changing q y))) x + changing q y x=0
 rw [←decided _ hq]; simp
lemma ordinary_square [FiniteDimensional ℝ E] (q:Quadratic (E×F))(hq:(core q).RespectsPrice)(x y): q.flourish (x+skew q hq y,y)=(core q).flourish x + (reduced q hq).flourish y:=by
 rw [show (x+skew q hq y,y)= (x,0)+(skew q hq y,y) by simp,biplus,q.side (x,0), square_snd]; rw [mul_zero,add_zero]; rfl
lemma pin_me [FiniteDimensional ℝ E] (q:Quadratic (E×F))(hq:(core q).RespectsPrice)(y:F) (d:E)(h:∀u:E,q.flourish (u+d,y)=(core q).flourish u+ q.flourish (d,y)): d=skew q hq y:= by
 let p:=skew q hq y; let s:= (core q).flourish (d-p); let t:= (core q).flourish (p-d);
 have ha:=h (p-d); rw [sub_add_cancel] at ha
 have he:= ordinary_square q hq (d-p) y; change q.flourish (d-p+p,y)= s + q.flourish (p,y) at he; rw [sub_add_cancel] at he;
 by_contra! H
 have hb:0<s:= definite _ hq _ (sub_ne_zero.mpr H); have hc:0<t := definite _ hq _ (sub_ne_zero.mpr (Ne.symm H)); change q.flourish (p,y)= t+ q.flourish (d,y) at ha; linarith
section Lift
-- `a` joint quadratic split by `e` on the fast coordinates ONLY.
-- `q` price in first block, `b` price in successive book with reduced price from `q`,
-- `χ` accounts for the skew evaluated on successive-row open field & remaining here.
variable (e:(F×B)≃ₗ[ℝ] E) (q: Quadratic F)(a:Quadratic (E×Y))(b:Quadratic (B×Y)) (χ:(B×Y)→ₗ[ℝ] F)
structure Charged : Prop where
 due x w y: a.flourish (e (x + χ (w,y),w),y)= q.flourish x + b.flourish (w,y)

 def pulley : (F×B)≃ₗ[ℝ] E:= LinearEquiv.trans
  { toFun:=fun u:F×B=> (u.1+ χ (u.2,0),u.2)
    invFun:=fun u:F× B=> (u.1-χ (u.2,0),u.2)
    map_add':=fun ⟨x,b⟩ ⟨y,c⟩=>Prod.ext (by
       change x+y+χ (b+c,0)=x+χ (b,0)+(y+χ (c,0)); rw [show (b+c,(0:Y))=(b,0)+(c,0) by simp,map_add]; abel) rfl
    map_smul':=fun r ⟨x,y⟩=> Prod.ext (by change r• x+χ (r•y,0)= r•(x+χ (y,0)); rw [show (r•y,(0:Y))=r•(y,0) by simp,map_smul,smul_add]) rfl
    left_inv:=fun x=>by simp
    right_inv:=fun x=>by simp } e
local notation "d"=> pulley e χ
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F][FiniteDimensional ℝ B]
variable (h:Charged e q a b χ)(hq:q.RespectsPrice)(hb:(core b).RespectsPrice)(ha:(core a).RespectsPrice)
namespace Charged
variable {e q a b χ}
include h
-- Lean stale variable carrying proofs when macros used. Explicit parameters
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ B] in
lemma stay (x w) : (core a).flourish ((d) (x,w))= q.flourish x + (core b).flourish w:= h.due x w 0

include hq hb in
lemma ticket : (core a).RespectsPrice:= by
 let p:= addOn (drag (LinearMap.fst ℝ F B) (recordQ hq.inner)) (drag (LinearMap.snd ℝ F B) (recordQ hb.inner))
 let hp : p.RespectsPrice := positiveProduct hq.inner hb.inner
 let f:= focusWith hp.inner (d).symm.toLinearMap (d).symm.injective
 refine ⟨f,records (core a) (recordQ f) ?_⟩; intro i; obtain ⟨⟨x,w⟩,rfl⟩:= (d).surjective i; rw [h.stay]
 change _=hp.inner.P ((d).symm ((d) (x,w))) ((d).symm ((d) (x,w))); rw [LinearEquiv.symm_apply_apply,decided _ hp]; change q.P x x+(core b).P w w= hq.inner.P x x+hb.inner.P w w; rw [decided _ hq, decided _ hb]

variable (e b χ) in
 def anchor (y:Y) : E := e (χ (skew b hb y,y),skew b hb y)

omit h in
lemma anchor_spend (x w y): (d) (x,w)+anchor e b χ hb y=e (x+χ (w+skew b hb y,y),w+skew b hb y):= by
 unfold anchor; change e (x+χ (w,0),w)+ _=_; rw [← map_add e,show (w+skew b hb y,y)=(w,0)+(skew b hb y,y) by simp,map_add χ]; rw [Prod.mk_add_mk,add_assoc]

lemma central (x w y) : a.flourish ((d) (x,w)+anchor e b χ hb y,y)= (core a).flourish ((d) (x,w))+ (reduced b hb).flourish y:= by rw [anchor_spend,h.due,ordinary_square _ hb,h.stay,add_assoc]
lemma centerQ (y:Y): skew a ha y=anchor e b χ hb y:= by
 symm; refine pin_me a ha y _ (fun u=>?_); obtain ⟨⟨x,w⟩,rfl⟩:= (d).surjective u; rw [h.central hb]; congr 1; symm; unfold anchor; rw [← show (0:F)+χ (skew b hb y,y)=_ from zero_add _,h.due,constant0,zero_add]; rfl
lemma reduced_eq (y:Y): (reduced a ha).flourish y=(reduced b hb).flourish y:=by change a.flourish (skew a ha y,y)=_; rw [h.centerQ hb ha]; simpa only [Prod.mk_zero_zero,map_zero,zero_add,constant0] using h.central hb 0 0 y

local notation "P₀"=> (fast ha.inner d)
local notation "K"=> (rest ha.inner d)

lemma free : fast ha.inner (d) = hq.inner:= by
 symm; apply RespectsPrice.pinpoints; apply records q (recordQ P₀); intro x;
 change _=ha.inner.P ((d) (x,0)) ((d) (x,0)); rw [decided _ ha]; symm; exact (h.stay x 0).trans (by simp [constant0])

lemma no_pin : pin ha.inner (d)=0:=by
 have hh (x w): ha.inner.P ((d) (0,w)) ((d) (x,0))=0:= by
  have hx: (core a).flourish ((d) (0,w)+(d) (x,0)) = (core a).flourish ((d) (x,0))+(core a).flourish ((d) (0,w)):= by rw [←map_add]; simp_rw [Prod.mk_add_mk,zero_add,add_zero,h.stay,constant0,zero_add,add_zero];
  rw [decided _ ha]; rw [biplus] at hx; change (core a).P _ _=0; linarith
 ext w; change -((P₀).inverse (mixed ha.inner (d) w)) = 0; rw [show mixed ha.inner (d) w = 0 from LinearMap.ext fun x => hh x w,map_zero,neg_zero]
lemma reserve : rest ha.inner (d)= hb.inner:= by
 symm; refine RespectsPrice.pinpoints hb (hp:= ?_) -- inspect arguments
 apply records _ (recordQ K); intro w;
 change _=ha.inner.P (shaft ha.inner d w) (shaft ha.inner d w); rw [namely,h.no_pin ha,LinearMap.zero_apply,decided _ ha]; symm; exact (h.stay 0 w).trans (by simp [constant0])
lemma reframe (x w): fusion ha.inner d (x,w)=(d) (x,w):= by
 change (d) (x+pin ha.inner d w,w)=_; rw [h.no_pin ha, LinearMap.zero_apply,add_zero];

variable [MeasurableSpace F][BorelSpace F][MeasurableSpace E][BorelSpace E][MeasurableSpace B][BorelSpace B]
variable (μ:Measure F)[μ.IsAddHaarMeasure](ν:Measure E)[ν.IsAddHaarMeasure](ρ:Measure B)[ρ.IsAddHaarMeasure]

lemma paid (p:Permit E): ha.inner.average ν p.val= hb.inner.average ρ fun y=> hq.inner.average μ fun x=> p.val ((d) (x,y)):= by rw [splice_int ha.inner (d) ν μ ρ _ (Papers.useful ν ha.inner p)]; simp_rw [h.reframe ha,h.free hq ha,h.reserve hb ha]

end Charged
end Lift
end YM.FVA2.Facade
