import YM.MSbar.Aqua.Oars
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "K"=>Primary n G
local notation "X"=>Positions (Primary n G)
variable {k p m s:ℕ}{D a b r w C C' B:ℝ}{A:Rep G n}{F:ℝ→ Config G n→ℝ}{f:Nesting G n}
variable (hF:Trend F f A.path A.clip p)(ha:Touch A.eval)
variable (x:Positions (Primary n G))(ρ:Site n→G.Color)
local notation "R"=>film A f r p
local notation "V₀"=>vine A r
local notation "W"=> fun i=> atlas f p i A.path A.clip
variable (hs:∀ i≤p,Stone G i k D B) (hk:∀ i:Body 1 n, ‖tint G _ (r • x) i‖<D)(hV:ContDiffAt ℝ k (vine A r) x)
variable (he:m+1≤ k)(hr:0<r)
include hF ha hs hk hV hr
local notation "Z"=> fun i=>sift ρ i r
local notation "I"=> Finset.range (p+1)
variable (hu:∀ i:Body 1 n, ‖tint G _ x i‖≤w)(hx:1 ≤ w)(hh:r ≤1)
include hu hx hh he
noncomputable def fCost (B r w:ℝ)(g:ℕ) := r^(g+1)*w^(g+1)*B
noncomputable def atoms (ρ:Site n→G.Color) := ∑ j:Primary n G, ‖ran ρ j.1‖
lemma pathC (Y Y':ℝ)(z:List K)(hz:z.length=m)(hc:∀ i≤ p,∀ v:Primary n G,∀ L:List K,L.length≤ m→ |buoy (W i) x (v::L)| ≤ Y)(hR:∀ v:Primary n G,∀ L:List K,L.length≤ m→ |buoy R x (v::L)| ≤ Y'):
     |buoy (aim R ρ) x z| ≤ 2^m*atoms ρ * fCost B r w 0*Y'+∑ i∈Finset.range (p+1), r^i*(2^m*atoms ρ *fCost B r w (p-i)*Y):=by
    let T':=I; let A' := atoms ρ; let H(i):= fCost B r w i
    have hF':ContDiffAt ℝ k R x:=hV.sub ((Aqua.pure ..).contDiffAt.of_le le_top); have hg(i:ℕ)(hi:i≤p):ContDiffAt ℝ m (Z i) x:= (comb ρ i x (hs i hi) _ hk).of_le (by exact_mod_cast (show m ≤ k from by omega))
    have hv(f:X→ℝ)(i:ℕ)(hi:i≤p)(v:ℝ)(hf:ContDiffAt ℝ k f x)(hh':∀ j:Primary n G,∀ L:List K,L.length≤ m→ |buoy f x (j::L)| ≤ v): |buoy (costP f (Z i)) x z| ≤ 2^m*A'*H i*v:=by
        refine le_trans (fife hf he (hg _ hi) (fun j=> H i*‖ran ρ j.1‖) ?_ hh' z hz) ?_
        · intro j L ht; have hp:= hs i hi; have hB:=hp.positive; apply (songs ρ i x j hp (hk _) hx (hu _) hr hh L (by omega)).trans
          unfold H fCost Lis.hits; split; rw [mul_one]; rw [mul_zero]; positivity
        rw [← Finset.mul_sum,show (∑ j:Primary n G, ‖ran ρ j.1‖)=A' from rfl]; exact le_of_eq (by ring)
    rw [boon hF ha x ρ hs hk hV he hr _ hz,abs_neg]; refine (abs_add_le ..).trans (add_le_add (hv R 0 (by omega) Y' hF' hR) ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun i hi=>?_))))
    have ht:= Nat.lt_succ_iff.mp (mem_range.mp hi); rw [abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]; exact mul_le_mul_of_nonneg_left (hv (W i) _ (by omega) Y ((vent ..).contDiffAt.of_le le_top) (hc i ht)) (pow_nonneg hr.le _)
omit he
include hu
local notation "S"=> swipe (Measuring.chart n G) a s
lemma sense (hp:m+2≤ k)(ht:x=0)(Y Y':ℝ)(h₁ :0≤a)(h₂:6 ≤ s)(v:Primary n G)(c:Strand G)(hc:∀ i≤ p,∀ j:Primary n G,∀ l:ℕ,l≤ m+1→ Yarn l (fun L:List K=> |buoy (W i) x (j::L)| * swipe (Measuring.chart n G) a s (j::L))≤ Y)(hR:∀ j:Primary n G,∀ l:ℕ,l≤ m+1→ Yarn l (fun L:List K=> |buoy R x (j::L)| *swipe (Measuring.chart n G) a s (j::L))≤ Y'):
    Yarn m (fun L:List K=> tide (v::L)*|buoy (aim R (ace v c)) x (v::L)|) ≤ 2*fCost B r w 0*solo m G*Y'+∑ i∈Finset.range (p+1),r^i*(2*fCost B r w (p-i)*solo m G*Y):=by
    let P:=ace v c; let H(i):= fCost B r w i; let V(i):= sift P i r; subst x
    have hF':ContDiffAt ℝ k R 0:=hV.sub ((Aqua.pure ..).contDiffAt.of_le le_top); have hg(i:ℕ)(hi:i≤p):ContDiffAt ℝ (↑(m+1:ℕ)) (V i) 0:= (comb P i _ (hs i hi) _ hk).of_le (by exact_mod_cast (show m+1 ≤ k from by omega))
    let fL(i:ℕ)(T:List K):= buoy (costP (W i) (V (p-i))) 0 (v::T); let F'(T:List K):=buoy (costP R (V 0)) 0 (v::T)
    have hx(T:List K):0 ≤ tide T:=by unfold tide; positivity  -- hx shadow
    have h₃(f:X→ℝ)(i:ℕ)(hi:i≤p)(w':ℝ)(hf:ContDiffAt ℝ k f 0) (hp':∀ j:Primary n G,∀ l:ℕ,l≤ m+1→ Yarn l (fun L:List K=> |buoy f 0 (j::L)| *S (j::L))≤ w'): Yarn m (fun L:List K=> tide (v::L)*|buoy (costP f (V i)) 0 (v::L)|) ≤ 2*H i*solo m G*w':=by
        have hv:0 ≤ H i:=by unfold H fCost; have hv:=hs i hi|>.positive; have hh:=‹1≤w›; positivity
        apply sole hf hp (hg _ hi) v (by omega) h₁ (by positivity) hp'; intro j T hT; apply (songs P _ 0 j (hs _ hi) (hk _) ‹1 ≤ w› (hu _) hr hh T (by omega)).trans; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (raft v j c) hv) (hitsN ..)).trans_eq (by unfold H fCost; ring)
    calc
        _ ≤ Yarn m (fun T=>tide (v::T)*|F' T|)+∑ i∈ range (p+1),r^i*Yarn m (fun T:List K=> tide (v::T)*|fL i T|):=by
            simp_rw [← sheen]; rw [← franje,← pockets]; apply shiny; intro l hl; rw [boon hF ha 0 P hs hk hV hp hr _ (by rw [List.length_cons,hl]),abs_neg]; refine (mul_le_mul_of_nonneg_left ((abs_add_le ..).trans (add_le_add_right (Finset.abs_sum_le_sum_abs ..) _)) (hx (v::l))).trans_eq ?_; rw [mul_add,Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl (fun i hi=>?_); rw [abs_mul,abs_of_nonneg (pow_nonneg hr.le _)]; unfold fL V; ring
        _ ≤ _:= add_le_add (h₃ _ 0 (by omega) _ hF' hR) (Finset.sum_le_sum fun i hi=> by refine mul_le_mul_of_nonneg_left (h₃ _ (p-i) (by omega) Y ((vent ..).contDiffAt.of_le le_top) (hc i (Nat.lt_succ_iff.mp (mem_range.mp hi)))) (pow_nonneg hr.le _))
end YM.MSbar.Aqua
