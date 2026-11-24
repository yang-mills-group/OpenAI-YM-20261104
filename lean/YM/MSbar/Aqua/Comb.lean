import YM.MSbar.Aqua.Stone
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
open Work.G05
variable {d w a b C B r:ℝ}{q k m:ℕ}
local notation "E"=>Positions (Primary n G)
local notation "Λ"=>Native.Chart.Rail G
local notation "A"=>G.Color
local notation "K"=>Primary n G
variable (t:Site n→G.Color)(p:ℕ) (x:Positions (Primary n G))(i:Primary n G)
noncomputable def sift (t:Site n→G.Color)(p:ℕ)(r:ℝ)(i:E) : Positions (Primary n G):= speedsK t (r • i)-blockTaylor p (speedsK t) (r • i)
variable (h:Stone G p m d B)
local notation "S"=> tint G (Body 1 n)
local notation "X"=> r • (tune i)
lemma tether (r:ℝ) : tune i (sift t p r x)=crest G (ran t i.1) p ((r • tune i:E→L[ℝ] G.Color) x):=by
   let V:=tune i; let R:E:=r • x; let g:=Native.Chart.speed G (ran t i.1); have ht: V (speedsK t R)=g (V R):=rfl; unfold sift crest; rw [map_sub, Pi.sub_apply]; change V (speedsK t R)-_=g ((r • V) x)-_; rw [ht]
   have hV: V R=(r • V) x:= V.map_smul r x; rw [← hV]; change g _ -V (blockTaylor p (speedsK t) R)= g _-blockTaylor p g (V R); congr 1
   unfold blockTaylor; rw [Finset.sum_apply,map_sum, Finset.sum_apply]; refine Finset.sum_congr rfl fun j hj=> ?_
   ext a; exact compass j t R (i.1,a)
include h
local notation "W"=> (X:E→L[ℝ] G.Color)
lemma comb (r:ℝ)(hk: ∀ i:Body 1 n, ‖tint G (Body 1 n) (r • x) i‖<d) : ContDiffAt ℝ m (sift t p r) x:=by
    let W':=sift t p r; apply contDiffAt_pi.mpr; intro i
    let K₀:E→L[ℝ] G.Color:= r • tune i; let f(v:E):= W' v i
    let L:= EuclideanSpace.proj (𝕜:=ℝ) i.2; have he:f= L ∘ crest G (ran t i.1) p ∘ K₀:=by funext y; apply congrArg (fun v:A=> v i.2) (tether t p y i r)
    change ContDiffAt ℝ m f x; rw [he]; apply L.contDiff.contDiffAt.comp; exact (vivid G (ran t i.1) (K₀ x) h.beam ((by have ht:= hk i.1; rw [map_smul] at ht; exact ht)) p m).comp x K₀.contDiff.contDiffAt
variable (hs : ‖tint G (Body 1 n) (r • x) i.1‖<d)(hx:1 ≤ w)(hh:‖tint G (Body 1 n) x i.1‖ ≤ w)(hr:0<r)(hR:r≤1)
include hr hR hx hh hs
noncomputable def tale (t:Site n→G.Color)(p:ℕ)(r:ℝ)(i:Primary n G)(x:E):= sift t p r x i
local notation "Z"=> tale t p r
local notation "C'"=> r^(p+1)*w^(p+1)*B
lemma songs (L:List (Primary n G))(hl:L.length ≤ m) : |buoy (tale t p r i) x L| ≤ r^(p+1)*w^(p+1)*B*‖ran t i.1‖*Lis.hits i L:=by
   let v:=ran t i.1; let f:=crest G v p; let E':= EuclideanSpace.proj (𝕜:=ℝ) i.2; have he:tale t p r i=(E' ∘ f) ∘ W:= by funext y;exact congrArg (fun v:A=> v i.2) (tether t p y i _)
   let l:= L.map fun j=> W (bolt j); have hX : (X) x=tune i (r • x):=by change r • tune i x=_; rw [map_smul]
   have hu: ContDiffAt ℝ m f ((X) x) := vivid G v (X x) h.beam (hX.symm ▸ hs) p m
   have hz:l.length=L.length:= List.length_map _; have hp:= E'.contDiff.contDiffAt (x:=f ((X) x))|>.comp (f:=f) ((X) x) hu
   unfold buoy; rw [he,toe _ m _ hp (by simpa only [List.length_map]),List.map_map]; unfold Lis.hits; split
   next hg=>
       rw [mul_one]; change |roc (E' ∘ f) l ((X) x)|≤ C'* _; rw [ores m l A E' f hu (by omega)]; refine (show |E' _| ≤ ‖roc f l ((X) x)‖ from PiLp.norm_apply_le (roc f l ((X) x)) i.2).trans ?_
       have he(j:Fin l.length): ‖l.get j‖≤r:=by
           obtain ⟨y,hy,hK⟩:= List.mem_map.mp (show l.get j∈ l from List.get_mem ..)
           rw [← hK]; change ‖r • tune i (bolt y)‖ ≤ _; rw [norm_smul,tuning,if_pos (hg _ hy),Lis.sunny,mul_one,Real.norm_of_nonneg hr.le]
       rw [rod m l ((X) x) hu (by omega)]; let D:= iteratedFDeriv ℝ l.length f ((X) x); have ht:‖(X) x‖ ≤ r*w:= by rw [hX,map_smul,norm_smul,Real.norm_of_nonneg hr.le]; exact mul_le_mul_of_nonneg_left hh hr.le
       have hW:‖D‖≤ B*‖v‖*(r*w)^(p+1-l.length):= (h.linger ((X) x) (hX.symm ▸ hs) _ (by omega) _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht _) (mul_nonneg h.positive (norm_nonneg _)))
       have hg : (∏ i:Fin l.length, ‖l.get i‖)≤ r^l.length:=by refine le_trans (Finset.prod_le_prod (fun i _=> norm_nonneg (l.get i)) (fun i _=> he i)) (by simp)
       let I:=p+1-l.length; have hp:0≤ B:= h.positive
       calc
            _ ≤ ‖D‖ *r^l.length:= (D.le_opNorm (l.get)).trans (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
            _ ≤ B*‖v‖*(r^(I+l.length)*w^I):=(mul_le_mul_of_nonneg_right hW (pow_nonneg hr.le _)).trans_eq (by unfold I; ring)
            _ ≤ _ := (mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_of_le_one hr.le hR (by exact (show p+1 ≤ I+l.length from by unfold I;omega))) (pow_le_pow_right₀ hx (by exact (show I ≤ p+1 from by unfold I; omega))) (by positivity) (by positivity)) (mul_nonneg h.positive (norm_nonneg _))).trans_eq (by unfold v; ring)
   next hk=>
      rw [mul_zero,abs_nonpos_iff]; change roc (E' ∘ f) l _=0; unfold allot at hk; push Not at hk; obtain ⟨j,hj,hq⟩:= hk; exact emptyF m _ l (List.mem_map.mpr ⟨j,hj,by change r • tune i (bolt j)=0; rw [tuning,if_neg hq,smul_zero]⟩) hp (by omega)
end YM.MSbar.Aqua
