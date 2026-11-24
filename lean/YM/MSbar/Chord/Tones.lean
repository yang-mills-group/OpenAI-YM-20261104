import YM.MSbar.Chord.Mill
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}
local notation "S₀"=> Site n
local notation "E"=> Edge (Site n)
local notation "N"=> n.val
noncomputable def bill (s : Signed)(X:List Axis):ℝ:= (X.map (StressFlux.sign s)).prod -- edit
noncomputable def mold (X:List Axis)(x y:E) := (X.map (middle x y)).prod
private lemma powerH (x:E)(y:E)(i j:ℕ) : beadPad x.1 y.1 (i+j)=beadPad x.1 y.1 i *beadPad x.1 y.1 j:=by unfold beadPad; ring
lemma castA (X:List Axis)(x y:E) : |mold X x y| ≤ beadPad x.1 y.1 X.length :=by
    induction X with
    | nil=>simp [mold,beadPad]
    | cons a L IH=>
       rw [show mold _ _ _= middle x y a * mold L x y by simp [mold], abs_mul]; refine (mul_le_mul (medium_size ..) IH (abs_nonneg _) ?_).trans_eq ?_; · unfold beadPad;positivity
       rw [List.length_cons, powerH]; ring
lemma sumEdge (d:Axis)(f : E→ℝ): ∑ i: Site n,f (i,d) = ∑ i:E,if i.2=d then f i else 0:=by rw [Fintype.sum_prod_type]; simp
-- rows interpreted with literal color.Set x fixed. 
variable {Q:FaceRail n G}{Z:ℝ}
local notation "j₀"=> cell Q
noncomputable def Moment (Q:FaceRail n G) (b:E)(c:Axis)(u v:G.Color)(X:List Axis):= ∑ i:Site n, cell Q b (i,c) u v * mold X b (i,c)
-- Ledger poly.
def Weigh (Q:FaceRail n G) (κ:ℝ):Prop:=∀ a:Edge (Site n),∀ (b:Axis),∀ u v:G.Color, ‖u‖=1 → ‖v‖=1 → ∑ i:Site n,|cell Q a (i,b) u v| *beadPad a.1 i 6 ≤κ
noncomputable def tumbler (c:Side)(κ:ℝ):= 100^3*κ/(c.val:ℝ)^3
variable (x:Edge (Site n))(c:Axis)(u v:G.Color)
lemma grow_tail (n:Side)(x y:Site n)(he: n.val ≤ 100*(separation x y+1)) : beadPad y x 3*(n.val:ℝ)^3 ≤ 100^3*beadPad y x 6:=by
    let z:ℝ:=1+separation x y; have hz:0 ≤ z:=by unfold z; positivity
    have hp:(n.val:ℝ)≤100*z:=by unfold z; exact_mod_cast (show n.val ≤ 100*(1+separation x y) by omega)
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp 3) (pow_nonneg hz 3)).trans_eq (by change z^3*(100*z)^3=_*z^6; ring)
variable (Y:Site n→ℝ)(h: Ribbon Q)(hx:Weigh Q Z)(hu:‖u‖=1)(hv:‖v‖=1)
include hx hu hv
lemma values {C:ℝ}(hc:0≤ C)(hk:∀ i,Y i≠0 → n.val ≤100*(separation i x.1+1)∧ |Y i| ≤ C*beadPad x.1 i 3) : |∑ i,cell Q x (i,c) u v*Y i| ≤ C*tumbler n Z:=by
    let f i:=cell Q x (i,c) u v; let p:ℝ:= n.val; have hp:0<p:= by unfold p; positivity
    have hh(i) : |f i*Y i| *p^3≤ C*100^3*(|f i| *beadPad x.1 i 6):=by
       have hx:= abs_nonneg (f i); by_cases he:Y i=0; rw [he,mul_zero,abs_zero,zero_mul]; unfold beadPad; positivity
       rw [abs_mul,mul_assoc]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hk i he|>.2) (by positivity)) hx).trans; rw [mul_assoc C]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (grow_tail n i x.1 (hk i he|>.1)) hc) hx).trans_eq; ring
    apply (Finset.abs_sum_le_sum_abs ..).trans ?_ -- edit
    unfold tumbler; rw [← mul_div_assoc, le_div_iff₀ (pow_pos hp 3), Finset.sum_mul]; let D:= C*100^3; refine (Finset.sum_le_sum (fun i _=>hh i)).trans ?_; rw [← Finset.mul_sum, ← mul_assoc C]; exact mul_le_mul_of_nonneg_left (hx x c u v hu hv) (by positivity)
omit hx hu hv
lemma pads (s:Signed)(b:S₀)(y:E) (p:ℕ) (hp:p≤2): beadPad (sendEdge s b x).1 (sendEdge s b y).1 p ≤ 16*beadPad x.1 y.1 2:=by
   unfold beadPad; let q(s:ℕ):ℝ:=1+(s:ℝ); let p' (x y:E) := q (separation y.1 x.1); let z:=p' x y; let T:=p' (sendEdge s b x) (sendEdge s b y); have hT:1 ≤ T:=by unfold T p' q; simp
   have hz:1≤z:=by unfold z p' q;simp -- semicolon
   apply le_trans (pow_le_pow_right₀ hT hp); change T^2≤ 16*z^2; have h:T ≤ 4*z:=by
       have hh':T≤ z+2:=by
           unfold T p' q; unfold z p' q; exact_mod_cast (show 1 + separation (sendEdge s b y).1 (sendEdge s b x).1≤ 1+separation y.1 x.1+2 by have ht:=lanes s b y x; omega)
       linarith
   refine (pow_le_pow_left₀ (zero_le_one.trans hT) h 2).trans_eq (by ring)
end YM.MSbar.Midpoint
