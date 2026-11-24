import YM.MSbar.Tramp.Thaw
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Matrix
open Precision Gauge Midpoint Rolling Wave MvPolynomial Exterior Tree Wilson
open AnalyticBridge.VerifiedReset Native.Chart Tensor UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c n: Side}{S:StepData c n} (F: Forest S.ratio)
local notation "Π!"=>Positions (Primary n G)
local notation "A"=> Primary n G
local notation "W"=> Positions (Primary c G)
local notation "Ω"=> Positions (Cards G n)
local notation "T₀"=> cards0 G n
local notation "H"=>cardsH G n
local notation "U"=> slide G n
local notation "L₀"=> Measuring.chart n G
variable (R: Matrix (Body 1 n) (Body 1 c) ℝ)
noncomputable def plot (t:ℝ) (G:Gauge): Matrix (Primary n G) (Primary c G) ℝ:= (1-t) • maple R G+t • shuttle F R
noncomputable def mouth (t:ℝ) (G:Gauge) : Matrix (Cards G n) (Primary c G) ℝ:= Matrix.fromRows (plot F R t G) (Matrix.fromRows (runner (straighten S F R) G) 0)
local notation "Ω'"=>slide G n
variable (x:Positions (Primary c G)) (t:ℝ)
lemma turnPoint : T₀ (mouth F R t G*ᵥ x)=plot F R t G*ᵥ x:=rfl
lemma basePoint : H (mouth F R t G*ᵥ x)=(tint G _) (runner (straighten S F R) G*ᵥ x):=rfl
lemma along (x:W) (t:ℝ):HasDerivAt (fun y:ℝ=> plot F R y G*ᵥ x) (grad (H (mouth F R t G*ᵥ x))) t:=by
    rw [basePoint, ← euclid]; let p:= maple R G*ᵥ x; let q:= shuttle F R*ᵥ x
    have hh (y:ℝ): plot F R y G*ᵥ x= p+y • (q-p):=by
        unfold plot; rw [add_mulVec, smul_mulVec, smul_mulVec]; simp_rw [sub_smul,p,q, smul_sub,one_smul]; abel -- simp p
    rw [funext hh]; simpa only [one_smul] using! (((hasDerivAt_id' t).smul_const (q-p)).const_add p)
variable (P:Nesting G n)(T:PathData G)(l:Clip)(r p:ℕ){f:ℝ→ Wilson.Config G n→ℝ}(he:Trend f P T l p)(hh:r≤p)
local notation "φ"=>PowerSeries.coeff r (tariff n p l T P)
noncomputable def tweak (F:Forest S.ratio)(R:Matrix (Body 1 n) (Body 1 c) ℝ)(P: Nesting G n)(T:PathData G)(l:Clip)(r p:ℕ) (t:ℝ):=Rolling.rail (mouth F R t G) (devotion P T l r p)
noncomputable def mapPred (F:Forest S.ratio)(R:Matrix (Body 1 n) (Body 1 c) ℝ)(G:Gauge)(p' : Pot (Primary n G))(t:ℝ):= Rolling.rail (plot F R t G) p'
variable (q:Pot (Primary n G))
lemma vita : clue (mapPred F R G q t) x= clue q (plot F R t G*ᵥ x):=congr_fun (Rolling.clearL ..) q
include he hh
lemma splash : HasDerivAt (fun t:ℝ=>clue (mapPred F R G φ t) x) (clue (tweak F R P T l r p t) x) t :=by
    let Q:=(fun t:ℝ=> plot F R t G *ᵥ x); let y:=mouth F R t G*ᵥ x
    have hv: clue (tweak F R P T l r p t) x= clue (devotion P T l r p) (mouth F R t G*ᵥ x):= congr_fun (Rolling.clearL ..) _
    rw [hv,pursuit P T l r p he hh,turnPoint]; simp_rw [vita]; exact ((helm φ _|>.differentiable (show (1:WithTop ℕ∞)≠0 from (by simp)) (Q t)).hasFDerivAt.comp_hasDerivAt _ (along F R x t))
variable {m k:ℕ} {D a b w:ℝ}{s: Primary c G→ Site n}
variable (ha:0≤a)(hw:0<w)(h:∀ i< r, Tokew (slide G n ∘ Sum.inl) a m (k+1) 0 (PowerSeries.coeff i (tariff n p l T P)) D)
variable (ht:∀ t∈ Set.Icc (0:ℝ) 1,Syrup (slide G n) s a m (mouth F R t G) b)
local notation "Θ" =>∑ i∈Finset.range r, 2*2^k*tub G a m (r-i) (k+1)
include h ht ha
lemma swing : Tokew s a m k 0 (Rolling.rail (shuttle F R) φ - Rolling.rail (maple R G) φ) (b^(k+1)*(Θ*D)):=by -- Θ parser binder
   let U':= devotion P T l r p; let f(t:ℝ × W):= clue φ (plot F R t.1 G*ᵥ t.2); let Y:= (b^(k+1)* (Θ*D)); let Q:= Rolling.rail (shuttle F R) φ - Rolling.rail (maple R G) φ; let g(t):= tweak F R P T l r p t
   have hp : ContDiff ℝ ω f:=by
       let L (i:ℝ×W):=plot F R i.1 G*ᵥ i.2; refine (helm φ ω).comp (show ContDiff ℝ ω L from ?_)
       apply contDiff_pi.mpr; intro i; unfold L; simp only [Matrix.mulVec,dotProduct]; refine ContDiff.sum (fun j _=> (ContDiff.mul ?_ ((ContinuousLinearMap.proj j : W→L[ℝ]ℝ).contDiff.comp contDiff_snd))) -- parse
       change ContDiff ℝ ω (fun x:ℝ × W=>(1-x.1)*maple R G i j + x.1*shuttle (G:=G) F R i j); fun_prop
   have hx: Tokew Ω' a m k 0 U' (Θ*D):=pleasure P T l r p a m k D ha h -- placeholders
   have hf(t:ℝ)(v:t∈Set.Icc (0:ℝ) 1): Tin s a m k 1 (g t) Y:=by
       have he:=Tin.scaleT (ht t v) ha (by norm_num : (0:ℝ)<1) (Tin.lit zero_lt_one (le_refl 1) hx); refine Tin.it zero_lt_one he ?_ le_rfl; unfold Y; simp
   have hc: Tin s a m k 1 Q Y:=by
       refine glean f hp g ?_ Q ?_ zero_lt_one hf
       · intro x t; have hc:= splash F R x t P T l r p he hh
         simp_rw [vita] at hc; exact hc
       intro x; unfold clue Q; rw [_root_.map_sub]; change clue (Rolling.rail _ _) _-clue _ _= clue φ _-clue φ _; congr 1
       · have ht : shuttle (G:=G) F R=plot F R 1 G:=by simp [plot]
         rw [ht]; exact vita F R x 1 φ
       rw [show maple R G=plot F R 0 G from ?_]; exact vita F R x 0 φ; simp [plot]
   exact Tin.weightTok zero_lt_one le_rfl hc
end YM.MSbar.Tramp
