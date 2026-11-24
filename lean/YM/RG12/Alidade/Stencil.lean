import YM.RG12.Alidade.Teams
/-! # Precision bridge in charts at k. Quadratic arithmetic

Capture normalized reflected forms on the nonredundant pencils after a close-to-id STRICTLY
upper chart correction on filtration. Common through second order except for a universal
scale response at second order. No statement here this low-order coefficient law already proved
for the Wilson graph arrays! Allows polynomial meter costs in first and again second order
for the measurements themselves (not for the response, which needs just log-ratio with
universal leading constant). Expose coefficients explicitly as a development port: without
strictly lowering at order one, this bridge will NOT fix our matrix price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Frames Real
open scoped Topology BigOperators
variable (V:Type*)[NormedAddCommGroup V][NormedSpace ℂ V]
/-- Use real readings (evaluated as real part of sesqui, coincidence anomalies EXCLUDED).
Allows arbitrary grading; no Realization of rotation group required. -/
structure Tile where
   val : V → V →ℝ
   add (x y z:V) : val (x+y) z= val x z+val y z
   add' (x y z:V): val x (y+z)=val x y+val x z
   hom (x y:V)(a:ℝ): val ((a:ℂ) • x) y=a*val x y
   hom' (x y:V)(a:ℝ):val x ((a:ℂ) • y)=a*val x y

variable {V}
abbrev Form := Module.End ℂ V
structure Charge where
    zeroth: Tile V
    first : Tile V
    second : Tile V

structure Mixes where
    first : Form (V:=V)
    second : Form (V:=V)

local notation "X!"=> Form (V:=V)
variable (W:Charge (V:=V))(M:Mixes (V:=V))(x:V)
local notation "Y₀" => W.zeroth.val
local notation "Y₁" => W.first.val
local notation "Y₂" => W.second.val
local notation "H₁" => M.first
local notation "H₂" => M.second

def turned (t:ℝ): Form (V:=V):= LinearMap.id + (t:ℂ) • M.first + ((t^2:ℝ):ℂ) • M.second
lemma turn (t:ℝ): turned M t x=x+(t:ℂ) • H₁ x + ((t^2:ℝ) :ℂ) • H₂ x:=rfl
def axis (t:ℝ)(v :V):ℝ:=Y₀ v v+t*Y₁ v v+t^2*Y₂ v v
def windup (t:ℝ)(v:V):ℝ :=
    let a:=M.first v;let b:=M.second v
    axis W t v + t*(Y₀ a v + Y₀ v a) + t^2*(Y₀ b v+Y₀ v b+Y₀ a a+Y₁ a v+Y₁ v a)

structure Casket (v:ℝ) where
    hex : 1 ≤ v
    h (x:V): ‖M.first x‖ ≤ v*‖x‖
    a (x:V): ‖M.second x‖ ≤ v*‖x‖
    zero (x y:V) : |W.zeroth.val x y| ≤ v*‖x‖*‖y‖
    one (x y:V) : |W.first.val x y| ≤ v*‖x‖*‖y‖
    two (x y:V) : |W.second.val x y| ≤ v*‖x‖*‖y‖

lemma corner {v t:ℝ}(h:Casket W M v)(ht:0 ≤ t):‖turned M t x - x‖ ≤ v*(t+t^2)*‖x‖:=by
   have hx := norm_nonneg x
   rw [turn, show x+(t:ℂ) • H₁ x+((t^2:ℝ):ℂ) • H₂ x-x=(t:ℂ) • H₁ x+((t^2:ℝ):ℂ) • H₂ x from by abel]
   apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg ht, Real.norm_of_nonneg (sq_nonneg _)]
   exact (add_le_add (mul_le_mul_of_nonneg_left (h.h x) ht) (mul_le_mul_of_nonneg_left (h.a x) (sq_nonneg _))).trans_eq (by ring)

/-- explicit second-order truncation error when moving the chart. -/
lemma turns_page {v t:ℝ}(H:Casket W M v)(ht:0 ≤ t)(he:t≤1):
    |axis W t (turned M t x) - windup W M t x| ≤ 22 * v^3 * (t^2 * Real.sqrt t)*‖x‖^2:=by
   let a:=H₁ x; let c:=H₂ x
   let D(i:ℕ):V:=match i with
    | 0=>x
    | 1=>a
    | _=> c
   let Y(i:ℕ):=match i with
    | 0=>W.zeroth.val
    | 1=>W.first.val
    | _=>W.second.val
   let p(i j k:ℕ):= Y i (D j) (D k)
   let z:= v^3 * ‖x‖^2
   have hv:0 ≤ v:=zero_le_one.trans H.hex
   have hd(i):‖D i‖ ≤ v*‖x‖:=by unfold D; split; exact le_mul_of_one_le_left (norm_nonneg _) H.hex; exact H.h x; exact H.a x
   have hy(i)(x y:V):|Y i x y| ≤ v*‖x‖*‖y‖:=by unfold Y; split; exact H.zero x y; exact H.one x y; exact H.two x y
   have hp (i j k:ℕ): |p i j k| ≤ z:= by
      unfold p; apply (hy ..).trans; unfold z; exact (mul_le_mul (mul_le_mul_of_nonneg_left (hd j) hv) (hd k) (norm_nonneg _) (by positivity)).trans_eq (by ring)
   let g₃:=p 0 2 1+p 0 1 2+p 1 2 0+p 1 0 2+p 1 1 1+p 2 1 0+p 2 0 1
   let g₄:=p 0 2 2+p 1 1 2+p 1 2 1+p 2 1 1+p 2 2 0+p 2 0 2
   let g₅:=p 1 2 2+p 2 1 2+p 2 2 1
   let g₆:=p 2 2 2
   have hf : axis W t (turned M t x) - windup W M t x = t^3*g₃+t^4*g₄+t^5*g₅+t^6*g₆:=by
      unfold axis windup; dsimp only; rw [turn]; simp only [axis, Tile.add,Tile.add',Tile.hom,Tile.hom']
      dsimp only [g₃,g₄,g₅,g₆,a,c,p,Y,D]; ring!
   have h₃:|g₃|≤7*z:=by unfold g₃; calc
         _ ≤ |p 0 2 1|+|p 0 1 2|+|p 1 2 0|+|p 1 0 2|+|p 1 1 1|+|p 2 1 0|+|p 2 0 1|:=by repeat' first | exact le_rfl | apply (abs_add_le ..).trans; apply add_le_add
         _ ≤ _ := by linarith only [hp 0 2 1,hp 0 1 2,hp 1 2 0,hp 1 0 2,hp 1 1 1,hp 2 1 0,hp 2 0 1]
   have h₄:|g₄|≤6*z:=by unfold g₄; calc
         _ ≤ |p 0 2 2|+|p 1 1 2|+|p 1 2 1|+|p 2 1 1|+|p 2 2 0|+|p 2 0 2|:= by repeat' first | exact le_rfl | apply (abs_add_le ..).trans; apply add_le_add
         _ ≤ _ := by linarith only [hp 0 2 2,hp 1 1 2,hp 1 2 1,hp 2 1 1,hp 2 2 0,hp 2 0 2]
   have h₅ :|g₅|≤3*z:=by unfold g₅; calc
         _ ≤ |p 1 2 2|+|p 2 1 2|+|p 2 2 1|:=by repeat' first | exact le_rfl | apply (abs_add_le ..).trans; apply add_le_add
         _ ≤ _:=by linarith only [hp 1 2 2,hp 2 1 2,hp 2 2 1]
   have h₆:|g₆|≤1*z:=by rw [one_mul]; exact hp 2 2 2
   have he (i:ℕ)(hi:3≤ i)(x s:ℝ)(H : |x| ≤ s*z): |t^i*x| ≤ t^3*(s*z):=by
      rw [abs_mul,abs_of_nonneg (pow_nonneg ht _)]
      exact mul_le_mul (pow_le_pow_of_le_one ht he hi) H (abs_nonneg _) (pow_nonneg ht _)
   rw [hf]
   calc
    _ ≤ |t^3*g₃|+|t^4*g₄|+|t^5*g₅|+|t^6*g₆|:=by repeat' first | exact le_rfl | apply (abs_add_le ..).trans; apply add_le_add
    _ ≤ t^3*22*z:=by have h0:0 ≤ t^3*z:=by unfold z;positivity
                     linarith only [he 3 (by decide) g₃ 7 h₃,he 4 (by decide) g₄ 6 h₄,he 5 (by decide) g₅ 3 h₅,he 6 (by decide) g₆ 1 h₆,h0]
    _ ≤ _:=by
       have hτ:t ≤ Real.sqrt t:=by
          have hf:=Real.sqrt_nonneg t
          nlinarith [Real.sq_sqrt ht, show t≤1 by assumption]
       have hΓ := mul_le_mul_of_nonneg_left hτ (show 0 ≤ 22*v^3* t^2*‖x‖^2 by positivity)
       unfold z; linarith only [hΓ]

structure Second (s t e:ℝ)(early late:V→ℝ) : Prop where
    release : 0 < t
    law : t ≤ 1
    charter : Nonempty (Casket W M s)
    ledger : ∃ b:V→ℝ,(∀ x, |b x| ≤ e*‖x‖^2)∧ ∀ x,
               |late x - axis W t x| ≤ s*(t^2*Real.sqrt t)*‖x‖^2 ∧
               |early x - (windup W M t x+t^2*b x)| ≤ s*(t^2*Real.sqrt t)*‖x‖^2

variable {early late:V→ℝ}
-- discard first two order logs from all but anomaly `b`. require actual polynomial precision locally,
-- NOT Λ-small at lead tests in this application. Close with explicit loss.
lemma tuned_pair {s t e:ℝ}(H:Second W M s t e early late)(hv:s*(t+t^2)≤ 1)(x:V):
   let u:=t^2*Real.sqrt t
   |early x - late (turned M t x)| ≤ (27*s^3*u +e*t^2)*‖x‖^2:=by
   intro u; obtain ⟨h⟩:= H.charter; let f:=turned M t x
   have h0 := H.release.le; have hs:1 ≤ s:=h.hex; have hs': s ≤ s^3:=le_self_pow₀ hs (by norm_num)
   have hu :0 ≤ u:=mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg t)
   have he : ‖f‖ ≤ 2*‖x‖:=by
      rw [show f=f-x+x from by abel] -- rw expands f? ok
      apply (norm_add_le ..).trans; have hc:=corner W M x h h0
      have ha := mul_le_mul_of_nonneg_right hv (norm_nonneg x); change ‖f-x‖ ≤ _ at hc; linarith only [ha,hc]
   obtain ⟨Z,hZ,hx⟩:=H.ledger
   obtain ⟨hL,-⟩:=hx f; obtain ⟨-,hX⟩:=hx x
   have hf := turns_page W M x h h0 H.law
   calc _ ≤ (|early x-(windup W M t x+t^2*Z x)|+t^2*|Z x|)+|axis W t f-windup W M t x| + |late f-axis W t f|:=by
           have ht':0 ≤ t^2:=sq_nonneg _; rw [←abs_of_nonneg ht',←abs_mul,abs_of_nonneg ht'] -- erroneous rewrite occurrence
           have hg(a b c d e:ℝ): |a-e| ≤ |a-(b+c)|+|c|+|d-b|+|e-d|:=by
              rw [show a-e=a-(b+c)+c+ -(d-b)+ -(e-d) from by ring]
              simp_rw [← abs_neg (d-b),← abs_neg (e-d)] -- loop?
              apply (abs_add_le ..).trans (add_le_add _ le_rfl)
              exact (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
           convert hg (early x) (windup W M t x) (t^2*Z x) (axis W t f) (late f) using 1
        _ ≤ _ :=by
           have hτ:‖f‖^2≤4*‖x‖^2:=by nlinarith only [he,norm_nonneg x,norm_nonneg f]
           have he:=mul_le_mul_of_nonneg_left hτ (by have h0:0 ≤ s:=zero_le_one.trans hs;exact mul_nonneg h0 hu)
           change _ ≤ s*u*‖f‖^2 at hL; change _ ≤ s*u*‖x‖^2 at hX; change |axis W t f-windup W M t x| ≤ 22*s^3*u*‖x‖^2 at hf
           nlinarith only [he,hL,hX,hf,mul_le_mul_of_nonneg_left (hZ x) (sq_nonneg t),mul_le_mul_of_nonneg_right hs' (mul_nonneg hu (sq_nonneg ‖x‖))]
end YM.RG12.Alidade
