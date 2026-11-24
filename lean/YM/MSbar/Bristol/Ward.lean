import YM.MSbar.Cypress.Growth
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film -- remove
variable {G:Gauge}{c f:Side} {S:StepData c f} (R:Rep G c)(U:Nesting G c)
open Measuring
local notation "W"=>Positions (Primary c G)
local notation "K"=>Primary c G
variable (v:G.ColorIndex){i j k p o s:ℕ}{r w c1 c2 c3 t A b a Y C D h':ℝ}
variable {g:ℝ → Config G c→ℝ}(hT:Trend g U R.path R.clip p)(h:Keeps U p (sun G v))
local notation "R₀"=> Aqua.vine R r
local notation "P'"=> tariff c p R.clip R.path U
local notation "P"=>film R U r p
local notation "T"=>Measuring.chart c G
local notation "Y'"=> buoy P 0
local notation "η"=>rim (collectT c R.path R.clip)
noncomputable def priceS (s:ℕ)(r:ℝ) (R:Rep G c)(F:Nesting G c): Pot (Primary c G):= ∑ i∈range (s+1),r^i • PowerSeries.coeff i F
lemma pricesP : Aqua.ore R U r p= clue (priceS p r R (tariff c p R.clip R.path U)) := by
     funext x; unfold ore clue priceS; rw [_root_.map_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [← C_mul',_root_.map_mul,MvPolynomial.eval_C]; rfl
include h hT
lemma priceUP : caliper c (sun G v) (priceS p r R (tariff c p R.clip R.path U))= -caliper c (sun G v) (ink c R.clip R.path):=by
    unfold priceS tariff; rw [map_sum,Finset.sum_eq_single_of_mem 0 (mem_range.mpr (Nat.zero_lt_succ p))]
    · rw [pow_zero,one_smul,map_sub,PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.C _),PowerSeries.constantCoeff_C,hT.bond,zero_sub,map_neg]
    intro i hi hx; rw [map_sub,PowerSeries.coeff_C_of_ne_zero hx, sub_zero,_root_.map_smul,h.sitting i (Nat.lt_succ_iff.mp (mem_range.mp hi)),smul_zero]
variable (hr:0 < r)
variable {Ω:Set (Positions (Primary c G))} (hx:IsOpen Ω) (he:Convex ℝ Ω)(h0:(0:Positions (Primary c G))∈Ω)(hB:Bash Ω R.p)(hG:G.Simple)
variable (hm:R.beta*r^2=1) (hu:10*(p+4)< c.val) (hA:R.Lawful b A Y C D) (hj:R.p.B ≤ j)(ho:10*(s*(4*j+2)+2*j)< c.val)
noncomputable def prestige (e:G.Color) (X:Rep G c)(r ℓ b v:ℝ)(p j:ℕ):= r^2 * (2*ℓ*url c p b+ brim c X.p G j *v)
omit h hT
lemma sized (r:ℝ)(F:W→ℝ)(u:ℕ)(he:ContDiffAt ℝ 2 F 0): rim (fun x:W=>F (r • x))=r^2 • rim F:=by
     ext1 x; ext1 y; let L:W→L[ℝ]W:=r • ContinuousLinearMap.id ℝ W; have hf:L 0=0:=map_zero _; have he : ContDiffAt ℝ 2 F (L 0):=by rwa [hf]
     have ht :iteratedFDeriv ℝ 2 (F ∘ L) 0 ![x,y]=iteratedFDeriv ℝ 2 F 0 ![r • x,r • y]:=by rw [iter_lin_at he, hf]; change iteratedFDeriv ℝ 2 F 0 (fun i=> L (![x,y] i))=_; refine congr_arg (iteratedFDeriv ℝ 2 F 0) ?_; funext i; fin_cases i <;> rfl -- vec
     simp_rw [iteratedFDeriv_two_apply] at ht; change rim (F ∘ L) x y = _; change rim (F ∘ L) x y = rim F (r • x) (r • y) at ht; rw [ht,map_smul]; simp only [_root_.smul_apply,map_smul,smul_eq_mul]; ring
include hr hx he h0 hB hG hm hu hA hj ho h hT
lemma sizeR : |stackH c (sun G v) (rim (film R U r p))| ≤ prestige (sun G v) R r Y b C p s := by
    obtain ⟨hz,ht⟩:= climb R s j p hA hB (sun G v) (sunny ..) hG hx he h0 hu hj ho -- binder
    have hb : ContDiffAt ℝ (↑(2:ℕ)) (Aqua.vine R r) 0:=by
         let L:=r • ContinuousLinearMap.id ℝ W; have he:L 0=0:=map_zero _; exact (show ContDiffAt ℝ (↑(2:ℕ)) (walnut R) (L 0) from (by simpa only [he] using (show ContDiffAt ℝ (↑(2:ℕ)) (walnut R) 0 from hz))).comp 0 L.contDiff.contDiffAt
    have hf : rim (film R U r p)= r^2 • rim (walnut R)-stackP c G (priceS p r R (tariff c p R.clip R.path U)):=by
         unfold film; rw [← sized r _ 0 hz]; ext1 x; ext1 y; have he:= ((Aqua.pure R U r p).contDiffAt.of_le (m:= (↑(2:ℕ):ℕ∞ω)) le_top (x:=0)) -- sig
         rw [pricesP] at *; change rim (Aqua.vine R r- clue _) x y= rim (Aqua.vine R r) x y- rim (clue _) x y; exact Eq.trans (iteratedFDeriv_two_apply (R₀-clue (priceS p r R P')) 0 ![x,y]).symm (by rw [iteratedFDeriv_sub_apply hb he, _root_.sub_apply,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; rfl)
    let e:= sun G v; rw [hf,show (stackH c _) (_-_)= _ from (_root_.map_sub (stackH c (sun G v)) _ _), show stackH _ e (stackP _ _ _)= _ from (show stackH c e (stackP c G _)= -caliper _ e (ink c R.clip R.path) from priceUP R U v hT h),show (stackH _ _) (_ • _)=_ from (_root_.map_smul (stackH c (sun G v)) (r^2:ℝ) (rim (walnut R))),sub_neg_eq_add]; change |r^2*grossH (rim (walnut R)) e+ caliper _ _ _| ≤ _
    have hf: caliper c e (ink c R.clip R.path)= grossH (rim (collectT c R.path R.clip)) e:= congr_arg (stackH c e) (ion R.path R.clip hT.quiet); rw [hf]; refine le_trans (b:=r^2 * |grossH (rim (walnut R)) e+R.beta*grossH (rim (collectT c R.path R.clip)) e|) ?_ (mul_le_mul_of_nonneg_left ht (sq_nonneg _))
    rw [show r^2*grossH _ _ + grossH _ _= r^2 * (grossH (rim (walnut R)) e+ R.beta*grossH (rim (collectT c R.path R.clip)) e) from ?_,abs_mul,abs_of_nonneg (sq_nonneg r)] -- pattern
    rw [mul_add,← mul_assoc, mul_comm (r^2) R.beta,hm,one_mul]
end YM.MSbar.Bristol
