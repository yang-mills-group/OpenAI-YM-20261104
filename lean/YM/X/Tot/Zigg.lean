import YM.X.Tot.Knell
/-!
# ∑ torus holes and free single-line Bernstein cost. ∆budget. λ masks exclude at most one majority mark. vertex power weights included (here use e^4 ∑, wires normalized). Supports varying point emission.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed
open Stems hiding X
open Ocean Haze Friend Fielding Print Fund
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}{e:ℝ}
variable (χ:Floor R)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=> epsilon q
local notation "o"=> side q k
abbrev Weave (q:ℕ+):= (i:ℕ)→ Site (side q i)→ ℂ
def volS (q:ℕ+)(k:ℕ):ℂ:= (epsilon q k :ℂ)^4
lemma volS_visa : Chase q r 4 (Once (fun k=>volS q k)) := by
    simp_rw [volS, ← Complex.ofReal_pow]; exact Chase.com (by have h:= Chase.power (q:=q) (r:=r) 4; norm_cast at * )
def crow (q:ℕ+)(f:Weave q):ℕ→ℂ:=fun k=>volS q k * (∑ z:Site (side q k),f k z)
def bend (q:ℕ+) (χ:Floor R)(x:Fielding.Walk) : Weave q:= fun k z=> Complex.ofReal (χ.s (spot (epsilon q k) (lift (z-wrap (side q k) (x k)))))
local notation "Ξ"=> Weave q
variable (x: Fielding.Walk) (hq:1<q.val)(U V W:Weave q)
lemma crowd_plus : crow q (U+V)=crow q U+crow q V:= by ext1; simp [crow,Finset.sum_add_distrib,mul_add]
lemma crowd_sub : crow q (U-V)=crow q U-crow q V:= by ext1;simp [crow,Finset.sum_sub_distrib,mul_sub]
lemma crowd_scale (a:ℂ):crow q (a • U)=a • crow q U:= by ext1; simp [crow,Finset.smul_sum,smul_eq_mul,Finset.mul_sum,mul_left_comm]
lemma crowd_onto (p:I→Weave q)(b:Finset I) : crow q (∑ i∈b,p i)=∑ i∈b,crow q (p i):= by induction b using Finset.induction_on with| empty=>rw [Finset.sum_empty,Finset.sum_empty]; ext1 i; simp [crow]| insert j b hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,crowd_plus,ih]
lemma from_mul : fromX q x (U*V)=fromX q x U*fromX q x V:= rfl
lemma belt (h:∀ z∈(Floor.maskL q χ k).support,lift (wrap (side q k) z)=z): crow q (bend q χ x*U) k= influx (Floor.maskL q χ) (Once (volS q)*fromX q x U) k:= by
   rw [influx,←lift_band _ h]; unfold crow; let o':=wrap (side q k) (x k); conv_lhs=> rw [← Equiv.sum_comp (Equiv.addRight o')];
   rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold bend; simp only [Pi.mul_apply,Function.comp_apply,show Equiv.addRight o' i=i+o' from rfl, fromX,map_add,Floor.masking χ, add_sub_cancel_right,wrap_lift,Complex.real_smul]; unfold o'; rw [add_sub_cancel_right]; rw [add_comm i]; change _= _*(volS q k* _); ring
lemma single_seed (x:Fielding.Walk)(a:Marks G)(b:Tops G): fromX q x (wire q x a b)∈ seed q r 0 := by
   rw [rebaseW, sub_self]; let w:= 2+(a.k+b.k); let Y(n:Side)(x y:Cover):= spend n x y a.x b.x; let X(t:ℕ):=Complex.ofReal (epsilon q t ^(-(w:ℤ))); let K:= squall q Y; rw [show (fun (k:ℕ)(z:Cover)=> entryK (side q k) (epsilon q k) _ a z b)=Once X*K from ?_]; refine seeded Y (Once X) (enrolled₂ _ _ a.order b.order) (Chase.com ?_); unfold w; rw [show (0-(2+↑(a.k+b.k)):ℤ)= -(↑(2+(a.k+b.k)):ℤ) by omega]; exact Chase.power _
   ext1 t; ext1 z; rw [follow_r _ _ a b (epsilon_pos ..),div_eq_mul_inv,Complex.ofReal_mul]; simp only [K,X,squall,Once, Y,Pi.mul_apply,zpow_neg,zpow_natCast,mul_comm]; rfl -- Try
include hq
variable (hr:R<r)
include hr
lemma single_glint (hu:fromX q x U∈seed q r 0)(ht:Chase q r 0 (fromX q x V))(hp:Chase q r 0 (fromX q x W)): Released (crow q (bend q χ x*(U*V*W))):= by
    let B:= U*V*W; let L:= fromX q x; have hx:L B∈ seed q r 0:= by unfold L B;rw [from_mul,from_mul];simpa only [Int.add_zero] using! (fed hq (fed hq hu ht) hp)
    let b:= Once (volS q)*L B; have hg:= fed hq (g:=Once (volS q)) hx (volS_visa (q:=q)); rw [Int.zero_add,mul_comm] at hg; obtain ⟨m,hm⟩:= seed_rise hq χ hr (show b∈ seed q r 4 from hg); exact ⟨m,hm.congr' ((mask_global q χ hq).mono fun i he=> (belt χ _ B he).symm)⟩
lemma no_glint (h:Chase q r 0 (fromX q x U)): Released (crow q (bend q χ x*U)):= by
    let W:= Once (volS q)* fromX q x U; have he : Chase q r 4 W:= (volS_visa (q:=q)).mulC hq h; obtain ⟨m,h⟩:= mask_won hq χ (he.visa χ.positive.le hr) (by norm_num) (by norm_num); exact ⟨m,h.congr' ((mask_global q χ hq).mono fun i he=> (belt χ x U he).symm)⟩
end YM.PositionX.Tot
