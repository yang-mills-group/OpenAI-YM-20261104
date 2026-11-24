import YM.X.Chir.Civic
/-!
# Large-z support and uniform error in fixed regulator limit. polynomials.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open Maxwell (Green)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
local notation "T"=>Tet
local notation "o"=>side q k
local notation "D"=>Interval.mass
local notation "Tτ"=> transit q
variable {t u v w:Tet}{X Y Z:Fielding.Walk}{x y z:E4}
structure Zone (x y z:E4):Prop where
    x0 : ‖x‖≤1
    y0 : 8 ≤ ‖y‖
    y1 : ‖y‖ ≤ 9
    z1:4096≤ ‖z‖
namespace Zone
variable (h:Zone x y z)
local notation "d"=> ‖z‖
include h
lemma z0 : 0 < ‖z‖:= by linarith only [h.z1]
lemma wide_xy : 7 ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ 10:= by
    have hx:=norm_sub_norm_le y x; have hy:=norm_sub_le x y; rw [norm_sub_rev y x] at hx; constructor <;> linarith only [h.x0,h.y0,h.y1,hx,hy]
lemma wide_zx : ‖z‖/2 < ‖z-x‖:= by linarith only [norm_sub_norm_le z x,h.x0,h.z1]
lemma wide_zy : ‖z‖/2 < ‖z-y‖:= by linarith only [norm_sub_norm_le z y,h.y1,h.z1]
lemma wow : 4<‖x-y‖∧4<‖x-z‖∧4<‖y-z‖:= by rw [norm_sub_rev x z,norm_sub_rev y z]; have h0:= h.wide_zx; have h1:= h.wide_zy; have hx:= h.wide_xy.1; have hz:=h.z1; refine ⟨?_,?_,?_⟩ <;> linarith
lemma xy : x≠y:= sub_ne_zero.mp (norm_pos_iff.mp (lt_trans (by norm_num) h.wow.1))
lemma xz : x≠z:= sub_ne_zero.mp (norm_pos_iff.mp (lt_trans (by norm_num) h.wow.2.1))
lemma yz : y≠z:= sub_ne_zero.mp (norm_pos_iff.mp (lt_trans (by norm_num) h.wow.2.2))
lemma geometry (hx:plot q X x)(hy:plot q Y y)(hz:plot q Z z) : Geom q 4 X Y Z:= ⟨⟨_,_,hx,hy,h.wow.1⟩,⟨_,_,hy,hz,h.wow.2.2⟩,⟨_,_,hz,hx,norm_sub_rev z x ▸ h.wow.2.1⟩⟩
variable (hq:1<q.val)(hx:plot q X x)(hy:plot q Y y)(hz:plot q Z z)
local notation "H"=> Imprint.segment q
include hq hx hy hz
lemma route: ∀ᶠ i in L, d/8 ≤ H X Z i ∧ 1 ≤ H X Y i ∧ remote (Tτ X i) (Tτ Y i) (Tτ Z i):= by
     have hh:= lower_leg hq hx hy h.wow.1 (by norm_num); have he:= upper_leg hq hx hy ((h.wide_xy.2).trans_lt (by norm_num : (10:ℝ)<11)); have hg:= lower_leg hq hx hz (c:=d/2) (by rw [norm_sub_rev]; exact h.wide_zx) (by positivity); -- h.z0 for nonneg norm!
     filter_upwards [hh,he,hg,(giant_leg hq hx hz h.xz).eventually (eventually_ge_atTop 128)] with i hi hI hv hl; refine ⟨by linarith only [hv],?_,hl,?_⟩; · norm_num at hi; exact hi -- eq_div_div nonsense
     apply le_of_mul_le_mul_left (a:=ε i) ?_ (epsilon_pos q i); rw [mul_left_comm]; change 8*H X Y i ≤ H X Z i; linarith only [hI,hv,h.z1]
end Zone
structure Crowd (q:ℕ+)(x y z:E4)(J:Ter):Prop where
    openWide : Zone x y z
    traced : ∃ X Y Z, plot q X x∧plot q Y y∧plot q Z z∧RootJ q X Y Z J
variable (t u v w:Tet)(hq:1<q.val)
include hq
lemma rich : ∃ c:ℝ,c≥0 ∧ ∀ {x y z:E4}{J:Ter}, Crowd q x y z J→ ‖J t u v w-solar (z-x) w t * (η u t v * Green (x-y))‖ ≤ c*(‖z‖⁻¹)^5:= by
    obtain ⟨c,hc,H⟩:=sunroom hq t u v w; refine ⟨c*(8:ℝ)^5,by positivity,?_⟩; intro x y z J P; obtain ⟨h,X,Y,Z,hx,hy,hz,H0⟩:=P
    refine le_of_tendsto_of_tendsto ((H0 t u v w).sub ((turbine hq h.xz.symm hz hx w t).mul (trajectory u t v hq h.xy hx hy))).norm tendsto_const_nhds ?_
    filter_upwards [H,h.route hq hx hy hz] with i hi hg; apply le_trans (hi (Tτ X i) (Tτ Y i) (Tτ Z i) hg.2.2); let F:= Imprint.segment q X Z i; let G:= Imprint.segment q X Y i; change c* F⁻¹^5 * G⁻¹ ≤ _; have hf:0 < F:= rather; have he:0 < G:= rather; have hx:=h.z0; calc
      _ ≤ c*(‖z‖/8)⁻¹^5 * (1:ℝ)⁻¹:= by gcongr; exact hg.1; exact hg.2.1
      _ = _:= by simp [inv_div, div_eq_mul_inv,mul_pow,mul_assoc]
end YM.PositionX.Chir
