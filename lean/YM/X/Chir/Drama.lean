import YM.X.Chir.Slips
/-!
# authenticated bias ∥ ≤ dist^-5. first moment measurement weighted.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Imprint
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R t c:ℝ}
local notation "S"=>Site n
local notation "D"=>Interval.mass
local notation "p"=>fund
variable (x y z:Site n)(hc:c≥0)
local notation "b"=> D x z
local notation "g"=> lens b z
include hc
variable (F G:Site n→ℝ)
def outset (x z:S)(F:S→ℝ)(w:S):= (1-lens (D x z) z w)*F w-F x
local notation "A"=>p 5 x z
lemma wave_wide (h:Paying z 4 c F) (hp: PreachY 5 z F c) (w:S): ‖outset x z F w‖≤ 70000*c* A* D x w:= by
    let t:= p 4 x z; have hP:=live (k:=4) x z; have ht:=live (k:=5) x z; have he:=pay_pos x z; by_cases hu:D x w≤D x z/16
    · rw [outset,lens_off z w he ?_,sub_zero,one_mul]; exact le_trans (postage x w z _ hc hu hp) (by have hh:=pay_pos x w; gcongr; norm_num); have hh:=tip x w z; rw [comm w z] at hh; linarith
    let u:=D x w; unfold outset; have hy: ‖F x‖≤ c*p 4 x z:= by rw [funds]; exact h x
    have hh: ‖(1-g w)*F w‖ ≤ c*(4096*p 4 x z):= by
         by_cases hz:g w=1; · rw [hz, sub_self,zero_mul,norm_zero]; have h:=live (k:=4) x z; positivity
         have hh:= lenses (r:=b) z w; rw [norm_mul, Real.norm_of_nonneg (by linarith only [hh.2] : 0 ≤ 1-g w)]; apply le_trans (mul_le_mul_of_nonneg_right (by linarith only [hh.1] : 1-g w≤1) (norm_nonneg (F w))); rw [one_mul]; refine le_trans (h w) (mul_le_mul_of_nonneg_left ?_ hc); have hx:b/8 < D z w:= lt_of_not_ge (fun h=>hz (lens_white z w he h)); convert! justice (k:=4) x z z w 8 (by linarith only [hx]) using 1;norm_num
    apply (norm_sub_le ..).trans; refine le_trans (add_le_add hh hy) ?_; rw [← raising (k:=4) x z]; have hx:=lt_of_not_ge hu; change ¬ D x w ≤ _ at hu; nlinarith only [mul_le_mul_of_nonneg_right (show 4097*b ≤ 70000*D x w from by linarith only [hx,he]) (mul_nonneg hc ht.le)]
lemma out_cost (X:S→ℝ)(s:Finset S)(ht:Paying z 4 c X)(hP: PreachY 5 z X c)(hp:Paying x 3 c F)(hq:Paying y 3 c G): ‖∑ u∈s,outset x z X u*(F u*G u)‖ ≤ (9800000000*c^3)*p 5 x z*p 1 x y:= by
     apply (norm_sum_le ..).trans; let a:= 70000*c*A*c^2; have he: 0≤a:= by unfold a; have hx:=live (k:=5) x z; positivity
     calc
       _ ≤ ∑ u∈s,a*(D x u*balance x y u):= by
           refine sum_le_sum fun u _=>?_ ; rw [show a*(D x u*balance x y u)=70000*c*A*D x u*((c*p 3 x u)*(c*p 3 y u)) from by unfold a balance;ring,norm_mul,norm_mul]; have hh:=wave_wide x z hc X ht hP u; have ht:=live (k:=3) x u; have hz:=live (k:=3) y u; have hy:=hp u; have h:=hq u; have he:= live (k:=5) x z; have h0:= pay_pos x u; gcongr <;> positivity
       _ ≤ a * (140000*p 1 x y):= by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (bal₁ ..) he
       _ = _:= by unfold a;ring
-- Lens powering final
local notation "τ" => (p 1 x y)
def turn (n:Side)(x y z:Site n)(F G P:Scaff):= ∑ w:Site n,(P n z w-P n z x)*(F n x w*G n y w)
local notation "L"=> turn n x y z
lemma d_turn (F G P:Scaff)(hP:NiceF F n 1 c)(hG:NiceF G n 1 c)(ht:NiceF P n 1 c)(hr:128≤ D x z)(hv:8*D x y≤D x z)(i:Axis)(h:NiceF (ds i P) n 2 c): ‖turn n x y z F G (ds i P)‖ ≤ (10^10*c^3)*A*p 1 x y:= by
    let f:=F n x; let u:=G n y; let l:=(ds i P) n z; let t:=P n z; rw [turn]; have he : ∑ w:S, (l w-l x)*(f w*u w)= (∑ w:S,outset x z l w*(f w*u w))+(∑ w:S,(t (w+step i)-t w)*(g w*(f w*u w))) := by rw [← Finset.sum_add_distrib]; apply sum_congr rfl; intro w _; change _= _*_+l w *(g w*_); unfold outset;ring
    change ‖∑ w:S,(l w-l x)*(f w*u w)‖ ≤ _; rw [he]; apply le_trans (norm_add_le ..); apply (add_le_add (out_cost x y z hc f u l Finset.univ (h z|>.1) (h z|>.2) (hP x|>.1) (hG y|>.1)) (spark_sum x y z hc hr hv f u (hP x|>.1) (hG y|>.1) (hP x|>.2) (hG y|>.2) i t (ht z|>.1))).trans; rw [show 6=5+1 from rfl, addF (k:=5)];
    have hx:= justice' (k:=1) x y x z (by linarith only [hv,pay_pos x y]); let a':ℝ:=p 1 x z; have hh:=live (k:=1) x z; have ht:=live (k:=5) x z; have ht': c^3≥0:=by positivity
    calc
       _ ≤ 9800000000*c^3*A*τ+(65536*c^3)*(A*τ)*750:= by gcongr
       _ ≤ _:= by nlinarith only [mul_nonneg (mul_nonneg ht' ht.le) (show 0 ≤ τ from (live x y|>.le))]
end YM.PositionX.Chir.Imprint
