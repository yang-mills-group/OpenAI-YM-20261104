import YM.SchemeRG11.Outer.Bag
/-! Integrated remainder with NO links from V into the tracked node. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Dock
open Function Filter Asymptotics Topology MeasureTheory Metric Set
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long Air North Wolt Sew
open scoped Classical Pointwise
variable {I:Type*}{G:Gauge}
local notation "D₁"=> Atoll.land G
variable {T: Align.Itinerary}{z:I→ E4} (s:Finset I)(t:Landmarks I) (p:I→pLabel G)(l:pLabel G)(B:Window)
-- all relative v. require 3R<‖z_j‖
def inside0 (T:Itinerary)(j k:Axis): Slate:=fun i x=> (T.gap i)^(-4:ℤ) * (D₁).avg ((D₁).neg.heat (Tree.cost x j k * stemZero (T.gap i) l)*aerial s (fun l=>castZero (T.gap i) (p l)) (fun a=>t a i))
variable {R:ℝ} [DecidableEq I]
omit [DecidableEq I] in
private lemma serve1(h:Footpath T t s z)(hR:R>0)(hh:∀i∈s,3*R<‖z i‖): Gate.Lots T Prod.fst Prod.snd (fun _=>1) (S:= Funds (Near T R)) (Z:=spanX (G:=G) s (cords T t)):=by
 let r:=R/4; have hr : r>0:=by unfold r; linarith
 have he(k:I)(hk:k∈s):hops T (Near T R) r Prod.snd (fun x=>t k x.1):=by
    filter_upwards [(Tendsto.norm (h k hk)).eventually (lt_mem_nhds (hh _ hk))] with i hi x hx
    have hu:=cord T i (x-t k i)
    rw [inc_sub,norm_sub_rev] at hu
    let a:= incVec (T.gap i) x; let b:= incVec (T.gap i) (t k i)
    change ‖b-a‖ ≤ _ at hu; change 3*R<‖b‖ at hi
    have hA:‖a‖ ≤ 2*R:= (cord T i _).trans (mul_le_mul_of_nonneg_left hx (by norm_num))
    change R/4≤ baseU T i (x-t k i); linarith [norm_sub_norm_le b a]
 apply feed s t _ r _ _ hr he; intro a ha
 refine ⟨(r⁻¹)^2, by positivity,(he a ha).mono fun i H p h=>?_⟩; rw [←mul_pow]; calc _ = (1:ℝ)^2 := by norm_num
                                                                                           _ ≤ _:= by gcongr; rw [inv_mul_eq_div,one_le_div hr]; exact H _ h
private lemma segment (T: Itinerary)(m:ℕ):stemZero (G:=G) (T.gap m) = vary (fun i=>lensLeg T i (fun _=>0) m):=by
 unfold lensLeg; simp only [flex_zero]
set_option maxHeartbeats 800000 in
lemma gasp (h:Footpath T t s z)(he:Spaced R z s)(hp:R>0)(hh:∀ i∈s,3*R<‖z i‖)(j k:Axis): Worth (Near T R) (fun p'=>inside0 s t p l T j k p'.1 p'.2):=by
 let S:= Funds (Near T R); let Z:= spanX (G:=G) s (cords T t)
 let W: Crawl→ vellum G:=fun i=>stemZero (T.gap i.1) l
 have hW:Gate (D₁) S Z W:=by
   unfold W; simp_rw [segment T]; apply Gate.guest; rintro a v ⟨i,hi,b,rfl⟩; apply (earned (f:=fun k=>(D₁).bed (lensLeg T a _ k) (lensLeg T b (t i) k)) _)
   have he : (0:E4)≠z i:=by intro p; specialize hh i hi; rw [←p,norm_zero] at hh; linarith
   simp_rw [lens_l]; exact intact (Along.base 0) (h i hi) he (high_probe _) (high_probe _)
 have H:= sailgate (D₁) (cords T t) S Z s (fun i hi k=>⟨i,hi,k,rfl⟩) (chair t s z h (he.distinct hp)) p _ (Gate.crust _ j k _ _ _ (serve1 s t h hp hh) hW)
 change (fun x:Crawl=> inside0 s t p l T j k x.1 x.2)∈ S; convert H using 1; funext x; rw [inside0,rocket,map_smul,smul_mul_assoc,map_smul]; simp only [one_pow,one_mul];rfl
lemma gutter (h:Footpath T t s z)(he:Spaced R z s)(hp:R>0)(hh:∀ i∈s,3*R < ‖z i‖)(j k:Axis)(x:ℕ → Cover)(y:E4)(hx:Along T x y)(hr:‖y‖≤2*R): Finishes (fun i=> inside0 s t p l T j k i (x i)):=by
 let Z:= spanX (G:=G) s (Scores T t)
 let W: array ℕ (Shaft G):=fun i=>stemZero (T.gap i) l
 have hW:Gate (D₁) Sew.Home Z W:=by
   unfold W; simp_rw [segment T]; apply Gate.guest; rintro a v ⟨i,hi,b,rfl⟩; have hy:(0:E4)≠z i:=by intro e; specialize hh i hi; rw [← e,norm_zero] at hh; linarith
   unfold Scores; simp_rw [lens_l]; exact intact (Along.base 0) (h i hi) hy (high_probe _) (high_probe _)
 have hu(i:I)(a:i∈s): y ≠ z i:= by intro v; specialize hh i a; rw [←v] at hh; linarith
 have H:= sailgate (D₁) (Scores T t) Sew.Home Z s (fun i hi k=>⟨i,hi,k,rfl⟩) (reachPrice s t z h (he.distinct hp)) p _ (Gate.crust _ j k _ _ _ (meal s t x y h hu hx) hW)
 change Finishes _ at H; convert H using 1; funext i; rw [inside0,rocket,map_smul,smul_mul_assoc,map_smul]; simp only [one_pow,one_mul];rfl
lemma gleams (h:Footpath T t s z)(he:Spaced R z s)(hp:B.rOut<R)(hh:∀ i∈s,3*R < ‖z i‖)(j k:Axis): Finishes (fun i=> (T.gap i)^4 * ∑ x∈gateY T R i,cove T B i x* inside0 s t p l T j k i x):=by
 let g:=inside0 s t p l T j k; let f:Crawl→ℝ:=fun p=> cove T B p.1 p.2
 let A:= cove T B * g; let S:=Funds (Near T R)
 have hR:=B.rOut_pos.trans hp
 have hf : f∈S:= ⟨1,zero_lt_one,Eventually.of_forall fun i p _=> (abs_of_nonneg B.nonneg) ▸ B.le_one⟩
 obtain ⟨C,hC,H⟩:= (S.mul_mem hf (show (fun x:Crawl=>g x.1 x.2)∈S from gasp s t p l h he hR hh j k))
 refine travellers (f:=A) (T:=T) ?_ (mul_nonneg hC.le (show 0≤ R^3 by positivity)) (gate_d ..) ?_ ?_
 · filter_upwards [past (T:=T) hp] with i hi x hx
   change cove T B i x * g i x=0; have He : cove T B i x=0:=not_ne_iff.mp (fun w=>hx ((gate_iff ..).mpr (hi _ w))); rw [He, zero_mul]
 · filter_upwards [H] with i hi z hz
   rw [gate_iff] at hz; exact mul_le_mul (hi z hz) (pow_le_pow_left₀ (mul_pos (T.positive _) (World.d_pos _)).le hz _) (pow_nonneg (mul_pos (T.positive _) (World.d_pos _)).le _) hC.le
 intro y hy; let x (i):=stake (T.gap i) y
 have e : Along T x y:= follows y
 by_cases ht : ‖y‖≤2*R
 · have he': Tendsto (fun i=> cove T B i (x i)) atTop (𝓝 (B y)):= B.continuous.continuousAt.tendsto.comp e
   exact Finishes.mul ⟨_,he'⟩ (gutter s t p l h he hR hh j k _ _ e ht)
 apply (Finishes.const 0).same; filter_upwards [(Tendsto.norm e).eventually (lt_mem_nhds (show B.rOut<‖y‖ by linarith))] with i hi; exact Eq.symm (mul_eq_zero_of_left (show cove T B i (x i)=0 from B.zero_of_le_dist (by rw [dist_zero_right]; exact hi.le)) _)
end YM.SchemeRG11.Dock
