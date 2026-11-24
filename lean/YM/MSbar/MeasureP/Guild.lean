import YM.MSbar.MeasureP.Jams
import YM.MSbar.MeasureP.Gambit
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Function Filter Lattice Gauge Push Uniform
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Whisk RG Precision Next.Free Exterior Laurent Bloch Cane
variable {ι:Type}{G:Gauge}{c n:Side}{g:Ratio c n}{κ p:ℕ}{η a E D b s Y:ℝ}
variable (P : Cross g.count (TypeFace 1) (TypeFace 1))
local notation "A"=>Primary n G
local notation "B"=>Primary c G
local notation "X"=>pension g P G []
local notation "L"=>(g.count.val:ℝ)
local notation "Φ"=>value a D η E p κ
local notation "f"=>Measuring.chart n G
local notation "y"=>Measuring.chart c G
local notation "π"=>swipe y a p
local notation "ψ"=>treasure g G a p
variable (x:Primary n G)(v:Primary c G)(h:Cane P D η a E κ p)
variable {m k:ℕ}(hk:k≤κ)(hh:0<k)(Z:List (Primary n G)→ℝ)(hZ:∀ i:Primary n G,Conde (target i) Y m k (fun l=>Z (i::l))) (hy:0≤Y)
noncomputable def crownB (G:Gauge)(E η D:ℝ)(κ:ℕ) := ((κ:ℝ)+1)*((max 1 (Fintype.card Axis:ℝ))^κ*(Fintype.card (Strand G):ℝ)*(E*Real.exp η*(Fintype.card (TypeFace 1)*D))) -- parse max fix
local notation "W"=>crownB G E η D κ
include h hk hh hZ hy
lemma monument : Yarn m (fun T:List B=> swipe y a p (v::T)*|Yarn m fun l:List A=> mos g P x v k l T*Z (x::l)|)≤ treasure g G a p x v*|pension g P G [] x v| *((W/L)^m*Y):=by
   let F:= yarn g P x; let I(t) := commit F m k (fun L' => Z (x::L')) t; have he:=score (target x) F (author g P x) (ψ x) (fun i=>grot_positive ..|>.le) ((E*Real.exp η*(Fintype.card (TypeFace 1)*D))/L) κ m (fun q hq i v=>mailed P x i v h q hq) (by have hp:=h.D0; have ht:0≤E:=zero_le_one.trans h.E0; positivity) (fun l hh i=> photo P x h l.length hh l i rfl) k hk hh Y hy (fun l=>Z (x::l)) (hZ x)
   simp_rw [← mul_div_assoc] at he -- folding W
   refine le_trans ?_ (mul_le_mul_of_nonneg_left he (mul_nonneg (grot_positive ..|>.le) (abs_nonneg _)))
   rw [←sheen]; refine shiny _ fun T hT=>?_ ; change _ ≤ ψ x v*|X x v| *((T.map (ψ x)).prod*|I T|)
   rw [show Yarn m _= X x v * I T from ?_]; swap; · unfold I commit; rw [←sheen]; refine stitch _ fun t _=>?_ ; unfold mos; ring
   rw [abs_mul]; refine (mul_le_mul_of_nonneg_right (woodward P x h (v::T)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq ?_; rw [List.map_cons,List.prod_cons]; ring
variable (hP:∀ i:Primary n G,Yarn m (fun l:List (Primary n G)=>|Z (i::l)| *swipe (Measuring.chart n G) b p (i::l))≤ s)(hS:0≤ s)(hb:a/(g.count.val:ℝ) ≤ b)(he:2≤g.count.val)(hp:k ≤ p)
local notation "C"=>2*(feed a η E D p κ m/L^m)*((4/L)^k)
include hP hS hb he hp
lemma element : Yarn m (fun T:List B=> swipe y a p (v::T)*|Yarn m fun l:List A=> Z (x::l)*beads X (x::l) (v::T)|) ≤ treasure g G a p x v*|X x v| *(C*s+(W/L)^m*Y):=by
   let K:= ψ x v*|X x v|; have h0:0≤K:= mul_nonneg (grot_positive ..|>.le) (abs_nonneg _)
   let R(T:List B)(l:List A):= beads X (x::l) (v::T)-mos g P x v k l T; let I(T:List B)(l:List A):= R T l*Z (x::l)
   let J(T:List B)(l:List A):= mos g P x v k l T*Z (x::l)
   have hY:Yarn m (fun T=>π (v::T)*|Yarn m (I T)|)≤ K*C*s:=by
       have hi:0 ≤ C:=by unfold feed; have hp:= specs P h; positivity
       calc
          _ ≤ Yarn m fun T=> Yarn m fun l=>π (v::T)*|I T l| :=by apply shiny; intro T _; rw [sheen]; exact mul_le_mul_of_nonneg_left (polished ..) (effect ..|>.le)
          _ ≤ K*C*Yarn m (fun l=>|Z (x::l)| *swipe f b p (x::l)):=by
              rw [pool,←sheen]; refine shiny m fun l hl=>?_ ; let k':=|Z (x::l)|
              have hp:=grand P x v h l hk hb hp hh (by exact_mod_cast he)
              rw [hl] at hp
              unfold I; simp_rw [abs_mul,←mul_assoc,poker]; exact (mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans_eq (by ring)
          _ ≤ _:= mul_le_mul_of_nonneg_left (hP x) (mul_nonneg h0 hi)
   change _ ≤ K*(C*s+(W/L)^m*Y); rw [mul_add,←mul_assoc]; refine le_trans ?_ (add_le_add hY (monument P x v h hk hh Z hZ hy)); rw [← pockets]; refine shiny m fun T _=>?_ ; change π _ *|_| ≤ _*|Yarn m (I T)|+_*|Yarn m (J T)|; rw [←mul_add,show Yarn m _=Yarn m (I T)+Yarn m (J T) from ?_]; apply mul_le_mul_of_nonneg_left (abs_add_le ..) (effect ..|>.le)
   rw [←pockets]; refine stitch _ fun l _=>?_ ; unfold I J R; ring
lemma guild : Yarn m (fun l:List B=> swipe y a p (v::l)*|shaft (m+1) X Z (v::l)|)≤ L^4*(Φ/L)*(C*s+(W/L)^m*Y):=by
   let B':= C*s+(W/L)^m*Y; have hi:0≤B':=by have hp:= specs P h; have he:=h.E0; have hE:0≤ E:=zero_le_one.trans he; have hb:=h.D0; unfold B' feed crownB; positivity
   let F(x:A)(T:List B):= Yarn m fun l:List A=> Z (x::l)*beads X (x::l) (v::T)
   calc
       _ ≤ Yarn m fun l:List B=>∑ x:A,swipe y a p (v::l)*|F x l|:= by refine shiny _ fun l _=>?_ ; unfold shaft; rw [twilled,←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (effect ..|>.le)
       _ ≤ (∑ x:A,ψ x v *|X x v|)*B':=by rw [scarves,Finset.sum_mul]; refine Finset.sum_le_sum fun x _=> element P x v h hk hh Z hZ hy hP hS hb he hp
       _ ≤ _:=mul_le_mul_of_nonneg_right (capC P h v) hi
-- high absolute Sup no Ward.V
omit hh hZ he hp hk hy hP
lemma thin(W₀:List A→ℝ)(hw:∀ l:List A,l.length=m+1→0≤W₀ l)(hA:∀ i:Primary n G,Yarn m (fun l:List A=> W₀ (i::l)*swipe (Measuring.chart n G) b p (i::l))≤ s) : Yarn m (fun T:List B=> swipe y a p (v::T)*ter (m+1) X W₀ (v::T))≤ s*L^4*(Φ/L)^(m+1):=by
    exact (preGold g f y X h.a0 hb (div_nonneg (specs P h) (by positivity)) (fun i=> capR P h i) (fun j=> capC P h j) W₀ _ hw hA hS v).trans_eq (by ring)
end YM.MSbar.Measuring
