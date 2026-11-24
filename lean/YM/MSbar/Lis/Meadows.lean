import YM.MSbar.Lis.Luna
import YM.MSbar.MeasureP.Guild
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Measuring Precision Bloch Exterior Laurent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {c n : Side} (g:Ratio c n) (P: Cross g.count (TypeFace 1) (TypeFace 1))
noncomputable def roll (G:Gauge) : Positions (Primary c G)→L[ℝ] Positions (Primary n G) := LinearMap.toContinuousLinearMap ((Matrix.toLin') (pension g P G []))
local notation "Φ"=>roll g P G
local notation "A"=>Primary n G
local notation "B"=>Primary c G
local notation "X"=> Positions A
local notation "V"=> Positions B
local notation "T"=>Measuring.chart n G
local notation "t"=>Measuring.chart c G
local notation "L"=>(g.count.val:ℝ)
variable (i: Primary n G) (v: Primary c G)
lemma vin : roll g P G (bolt v) i=pension g P G [] i v:=by change (∑ j:B,pension _ _ _ _ _ _* bolt v j)=_; simp [bolt,Pi.single_apply]
variable (f:Positions (Primary n G)→ℝ)
variable {E D hS s S b a w u Y η:ℝ}{q p k m κ:ℕ} (h:Cane P D η a E κ p) (ha:a/(g.count.val:ℝ)≤ b)(hx:2≤ g.count.val)
open Metric Set Cane
local notation "S₀"=>closedBall (0:X) w
local notation "S'"=>closedBall (0:V) u
local notation "K"=>pension g P G []
variable {Ω:Set (Positions (Primary n G))}{Ω':Set (Positions (Primary c G))}
variable (hw:0<w)(hu:0<u)(hT:JetTab (Measuring.chart n G) b p w Ω f m Y)
include h ha hw hu hT
lemma waterfall (hm: Set.MapsTo (roll g P G) Ω' Ω)(hf:∀ x∈Ω,ContDiffAt ℝ q f x)(he:m+1≤ q) : JetTab (Measuring.chart c G) a p u Ω' (f∘ roll g P G) m
      ((u/w)^(m+1)*(Y*L^4*(value a D η E p κ/L)^(m+1))):=by
    obtain ⟨hy,g',hg,hG⟩:= hT; let R(l):= ter (m+1) K g' l; let X':=(u/w)^(m+1); have hX:0<X':=by unfold X'; positivity
    refine ⟨by have hp:=specs P h; positivity,fun l=> X'*R l,fun l hl=> ?_,fun i=> ?_⟩
    · refine ⟨mul_nonneg hX.le (luster (m+1) (fun l HH=> mul_nonneg (hg _ HH|>.1) (abs_nonneg _))),fun x hx=>?_⟩; unfold buoy; change |buoy _ _ _| * _ ≤ _
      rw [paint f (roll g P G) l x q (hf _ (hm hx)) (by omega),shaft,hl, show (fun j i=>Φ (bolt i) j)=K from (funext (fun i=>funext fun j=>vin g P i j))]
      apply le_trans (mul_le_mul_of_nonneg_right (polished ..) (by positivity : 0 ≤ u^(m+1))); change _ ≤ X' * R l; unfold R ter; rw [← poker, ← sheen]; refine shiny _ fun j hh => ?_; rw [abs_mul]; change |buoy f (Φ x) j| *_*u^(m+1)≤ _; let i:= Φ x
      calc
        _ = X'*(|buoy f i j| *w^(m+1))*|beads K j l|:= by unfold X' i; rw [div_pow]; field_simp -- local notation not decl
        _ ≤ _:= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hg _ hh|>.2 _ (hm hx)) hX.le) (abs_nonneg _)).trans_eq (by ring)
    unfold R; change Yarn m (fun i'=> X'* _*swipe _ _ _ _ ) ≤ X'*_; simp_rw [mul_assoc]; rw [sheen]; refine mul_le_mul_of_nonneg_left ?_ hX.le; have h1:= thin P i h hy ha g' (fun l hl=> (hg l hl).1) hG; simpa only [mul_comm (swipe _ _ _ _), mul_assoc Y] using h1
variable (hZ:Ω={0})(hv:∀ i: Primary n G, Conde (target i) s m k (fun l=> buoy f 0 (i::l))) (hf: ContDiffAt ℝ q f 0)
include h ha hx hZ hv hf
local notation "σ"=>value a D η E p κ
lemma sparkle (he:m+1≤q)(hs:0 ≤ s)(hk:0<k)(hh:k≤κ)(hr:k≤p) : JetTab (Measuring.chart c G) a p u {0} (f∘ roll g P G) m
     (L^4*(σ/L)* (2*(feed a η E D p κ m/L^m)*((4/L)^k)*(Y/w^(m+1))+(crownB G E η D κ/L)^m*s)*u^(m+1)):=by
    have h0:=hT.1; have hp:0≤ Y/w^(m+1):=by positivity
    refine JetTab.grant (fun i=>?_) ?_ hu
    · have hi:=guild P i h hh hk (buoy f 0) hv hs (hT.count hw 0 (hZ ▸ mem_singleton 0)) hp ha hx hr
      rw [mul_div_cancel_right₀ _ (pow_pos hu (m+1)).ne']; refine le_trans (le_of_eq ?_) hi
      refine stitch _ fun T' hT'=>?_ ; have he' : (i::T').length=m+1:=by simp [hT']
      let u:= roll g P G; rw [paint f u _ _ q (by rw [map_zero]; exact hf) (he'.trans_le he),map_zero,he']; rw [show (fun i j=> u (bolt j) i)= K from funext (fun i=>funext (fun j=> vin ..)), mul_comm] -- defeq syntactic
    have hh:=specs P h; have hx:=h.E0; have hv:0≤E:=zero_le_one.trans hx; have ht:=h.D0; unfold feed crownB; positivity
end YM.MSbar.Lis
