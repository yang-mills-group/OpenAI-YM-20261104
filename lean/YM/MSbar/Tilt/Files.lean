import YM.MSbar.Tilt.CostK
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tilt
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua Bout
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "P"=>Primary n G
local notation "W"=>Positions P
local notation "L"=> tint G (Body 1 n)
variable (ρ:Site n→G.Color) (F: Rep G n)(f:Nesting G n)(X:Positions (Primary n G))(i:Primary n G)(p q:ℕ){A B C D E t:ℝ}
local notation "R"=>ore F f t p
local notation "z"=> fun i=> atlas f p i F.path F.clip
variable {u:ℝ→ Config G n→ℝ}(h:Trend u f F.path F.clip p)
include h
lemma timbre (t:ℝ)(y:W): fderiv ℝ (ore F f t p) y (speedsK ρ (t • y))=∑ i∈Finset.range (p+1),t^i*costP (atlas f p i F.path F.clip) (sift ρ (p-i) t) y:=by
     let g:= ore F f t p; let s:=speedsK ρ (t • y); let U(i:ℕ):= fderiv ℝ (z i) y
     have hx : fderiv ℝ g y=∑ i∈Finset.range (p+1), t^i • U i:=by apply (HasFDerivAt.fun_sum ..).fderiv; exact fun i _=>((vent ..|>.differentiable (by simp) y : DifferentiableAt ℝ (z i) y).hasFDerivAt.const_smul (t^i))
     rw [show fderiv _ _ _ = _ from hx,_root_.sum_apply]; unfold costP sift; simp_rw [map_sub, mul_sub, Finset.sum_sub_distrib,cancelP F f t p h y ρ, sub_zero];rfl
omit h
noncomputable def species (b:Body 1 n):Finset (Primary n G):= Finset.univ.image (fun i:G.ColorIndex=>(b,i))
private lemma cardS(i:Primary n G) : (species (G:=G) i.1).card≤G.lieDim:=by -- search
     unfold species; refine Finset.card_image_le.trans_eq ?_; rw [card_univ,Fintype.card_fin]
variable (hA:E ≤ B)(hB:0 < t)(ht:t ≤1)(hz:Stone G q 2 D B)(hp: t*A < D)(he:‖tint G _ X‖ ≤ A)(hc:1 ≤ A)(hC:∀ i:Body 1 n,‖ran ρ i‖ ≤ C)
include hB ht hz hp he hc hC
local notation "V₀"=> costP (atlas f p q F.path F.clip) (sift ρ q t)
-- tax for tangent. output p-q vs q fix.
lemma warrant {g:Positions (Primary n G)→ℝ}(hh :ContDiffAt ℝ 2 g X)(hU:∀ i:Primary n G,|fderiv ℝ g X (bolt i)| ≤ E)(hG:∀ i:Primary n G,∑ j:Primary n G,|buoy g X [j,i]| ≤ E) : |fderiv ℝ (costP g (sift ρ q t)) X (bolt i)|≤ fCost B t A q*C*((G.lieDim+1:ℕ)*E):=by
     have hs:= hz.positive; let T:= sift ρ q t; have hl(j:Body 1 n): ‖tint G _ (t • X) j‖ < D:=by rw [map_smul,Pi.smul_apply,norm_smul,Real.norm_of_nonneg hB.le]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ _).trans he) hB.le) hp
     let M:=fCost B t A q*C; let Z:= species (G:=G) i.1; have hV: ContDiffAt ℝ (↑(2:ℕ)) T X:= comb ρ q X hz _ hl; have hC':0 ≤ C:=(norm_nonneg _).trans (hC i.1); have hM : 0 ≤ M:=by unfold M fCost; positivity
     have ht'(j:Primary n G)(u:List P)(h:u.length≤2):|buoy (fun y:W=>T y j) X u|≤ M*Lis.hits j u:=by exact (songs ρ q X j hz (hl _) hc ((norm_le_pi_norm _ _).trans he) hB ht u h).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC _) (by unfold fCost; positivity : 0≤ fCost B t A q)) (hitsN ..))
     let v(j:P):=if j ∈ Z then M*E else 0
     have hh : ContDiffAt ℝ (↑(2:ℕ)) g X:=by exact_mod_cast hh
     have hy : ∑ j:P,v j ≤ G.lieDim * (M*E):=by -- `∑ image` syntax
         unfold v; rw [← Finset.sum_filter]; have hZ : Finset.filter (fun j:P=>j∈Z) Finset.univ=Z:=by ext i;simp
         rw [hZ,sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (cardS i)) (mul_nonneg hM ((abs_nonneg _).trans (hU i)))
     change |buoy (costP g T) X [i]| ≤ _; rw [show buoy _ _ _= _ from Aqua.lens hh (le_refl 2) (hV.of_le (show ((1:ℕ):WithTop ℕ∞) ≤ (↑(2:ℕ):WithTop ℕ∞) by exact_mod_cast one_le_two)) [i] rfl]; calc
        _ ≤ ∑ j:Primary n G,(v j + M * |buoy g X [j,i]|):=by
             refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _=>?_); rw [twilled,Fintype.sum_bool,twillz,twillz]; apply (abs_add_le ..).trans; refine add_le_add ?_ ?_
             · change |buoy (fun y=>T y j) X [i] * buoy g X [j]|≤ v j; rw [abs_mul]; have hv:=ht' j [i] (show 1≤2 from one_le_two); unfold Lis.hits allot at hv; split at hv; next h=>
                    unfold v; rw [if_pos]; exact mul_le_mul (hv.trans_eq (mul_one _)) (hU j) (abs_nonneg _) hM; refine Finset.mem_image.mpr ⟨j.2,mem_univ _,?_⟩; rw [← h i (List.mem_cons_self ..)]
               next ht=>
                    rw [mul_zero] at hv; rw [le_antisymm hv (abs_nonneg _),zero_mul]; unfold v; split; exact mul_nonneg hM ((abs_nonneg _).trans (hU i)); exact le_rfl
             change |buoy (fun y=>T y j) X [] * buoy g X [j,i]| ≤ M*_; rw [abs_mul]; exact mul_le_mul_of_nonneg_right ((ht' j [] (by simp)).trans_eq (by simp [Lis.hits,allot])) (abs_nonneg _)
        _ ≤ _:=by rw [Finset.sum_add_distrib,← Finset.mul_sum]; refine (add_le_add hy (mul_le_mul_of_nonneg_left (hG i) hM)).trans_eq ?_; change _= M*_;push_cast;ring
end YM.MSbar.Tilt
