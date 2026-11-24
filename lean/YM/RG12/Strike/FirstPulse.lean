import YM.RG12.Strike.Resonates
/-! # Cancel all critical coupons in one cubic V3 two-mark integration (2+1 attachments)

For two tested marked curvature columns, order of derivatives unrestricted but fixed.
Holding color fixed and factoring axis choices on spectator wires at each mark, there are
three ordered-slot structures in ∂_i A_j [A_i,A_j]. Internal derivative displaced towards vertex;
mark displacement signs factor commonly (accounts in outer assembly). Orientation/color signs not
needed at all up to here. Includes correction at BOTH marks, absolute convergence. Tests at
arbitrary separated continuum points, not profile/subselection matching or matrices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable (U V W:Foil)(L K S:Poke)
variable (χ:R→ℂ)(z:R)
-- K1 critical: vanishes for ANY remote exterior, even offshell Feynman product
lemma shave1 (D:Poke)(j:Axis4)(g:R→ℂ)(x:R)(t:ℝ)(hχ:Base χ)(ht:0<t):crit χ (leg U L j D) g (D.length+L.length+3) x t=0:=by
   let a:=D.length+L.length+3
   by_cases h:4≤a
   · unfold crit; rw [if_pos (show 4 ≤ a from h)]
     let n:=a-4; let w:=hunt χ t; let P:=gauge n (fun l=>barrage g l x); let q:ℂ:=(↑n.factorial)⁻¹
     let T(i:Axis4):=D++L++[i];let X(i:Axis4)(u:R):=w u * tube (T i) u * fall P u
     let c(i:Axis4):=2*U i j*q
     have hn(i:Axis4): n+2=(T i).length:=by unfold T n a at *; simp only [List.length_append,List.length_cons,List.length_nil]; omega
     have he(i:Axis4): (∫ u:R,X i u)=0:=resonance (dries hχ t ht) _ (hn i) _
     have hu(i:Axis4):Integrable (fun u:R=>c i* X i u) := ((weighted (w*tube (T i)) (withered (dries hχ t ht) _ (fun _ hy=> (vellum punct_open punct_field _ _ hy).continuousAt)) (fall_cont P))).const_mul _ -- definally?
     change (∫ u:R, w u * (leg U L j D u*(q*fall P u)))=0
     rw [show (fun u:R=> w u*(leg U L j D u*(q*fall P u)))=fun u=>∑ i:Axis4,c i* X i u from ?_]
     · rw [integral_finsetSum Finset.univ (fun i _=> hu i)]; simp only [integral_const_mul,he,mul_zero,Finset.sum_const_zero]
     funext u; unfold leg c X T; rw [sum_mul,mul_sum]; apply sum_congr rfl; intro i _;ring
   unfold crit;rw [if_neg h]
-- k2. merge positions and orders with slope clerks. ordinary Leg maps in V3/book
inductive Farm : Type
 | alpha -- derivative on contracted and other contracted undifferentiated i, exterior j
 | beta -- derivative on contracted and other contracted undiff j, exterior i (changes color order)
 | delta -- derivative exterior. undiff contracted both
variable (θ:Farm)(i j:Axis4)
def activeAt : Axis4 := match θ with | .alpha => j | .beta => j | .delta => i
def alsoAt : Axis4 := match θ with | .alpha => i | .beta => j | .delta => j
def farAt : Axis4 := match θ with | .alpha => j | .beta => i | .delta => j
-- list lengths constants in i
abbrev stung (θ:Farm)(i:Axis4):Poke:=match θ with | .delta=> [] | _=>[i]
abbrev spike (θ:Farm)(i:Axis4):Poke:=match θ with | .delta=> [i] | _=>[]
def coreR (U V:Foil)(L K:Poke)(θ:Farm)(i j:Axis4):R→ℂ:= leg U L (activeAt θ i j) (stung θ i)*leg V K (alsoAt θ i j) []
def farR (W:Foil)(S:Poke)(θ:Farm)(i j:Axis4):=leg W S (farAt θ i j) (spike θ i)
def ar (L K:Poke)(θ:Farm) :ℕ:=L.length+K.length+6+(stung θ 0).length
def af (S:Poke)(θ:Farm) :ℕ:=S.length+3+(spike θ 0).length
def profile (L K S:Poke) :ℕ:=L.length+K.length+S.length+6
lemma ranchA : Garden (coreR U V L K θ i j) (ar L K θ):=by
   rw [coreR,ar]; convert (Garden.lineage U L (activeAt θ i j) (stung θ i)).times (Garden.lineage V K (alsoAt θ i j) []) using 1; cases θ<;> simp [stung] <;> omega
lemma ranchB : Garden (farR W S θ i j) (af S θ):=by
   rw [farR,af];convert Garden.lineage W S (farAt θ i j) (spike θ i) using 1;cases θ<;>simp [spike];omega
-- remote derivative opening: barrage of leg W S j [i] taped from Clean jet (potential normalized 2 and all translations). actually replace fleg [] first.
lemma far_der (x:R)(hx:x≠0)(p:Poke): barrage (leg W S j [i]) p x=slate (cloud W S) x j (i::p):=by
   let f:=cloud W S j
   have hh : ∀ u:R,u∈puncture→ leg W S j [i] u=hit i f u:=fun y hy=>by
      unfold leg
      change _=barrage (cloud W S j) [i] y
      rw [ridges W S [i] j _ hy];rfl -- lists associative?
   rw [barrage_local (g:=hit i f) punct_open (x:=x) hx hh, show hit i f = barrage f [i] from rfl, ← barrage_append]
   exact rain_spin f punct_open (cloud_silk W S j) (List.perm_append_comm (l₁:=p) (l₂:=[i])) x hx
-- total contracted leg exponent → m, m−1 shift
lemma shave2 (x:R)(hx:x≠0)(t:ℝ)(hχ:Base χ)(ht:0<t)(hU:anti U)(hV:anti V)(hW:anti W):
    ∑ i:Axis4,∑ j:Axis4,crit χ (coreR U V L K θ i j) (farR W S θ i j) (ar L K θ) x t=0:=by
   let w:=hunt χ t; let P:=slate (cloud W S) x; let m:=score L K
   have he:= jets (cloud W S) punct_open (cloud_silk W S) (breezes W hW S) x hx m -- args
   have hw:Dried w:=dries hχ t ht
   let c(n:ℕ):ℂ:=(↑n.factorial)⁻¹
   cases θ with
   | alpha=>
     suffices hz:(∑ i:Axis4,∑ j:Axis4,_)=c m*rowA P L K U V w by rw [hz, sinkA, mul_zero] <;> assumption -- underscores testing
     unfold rowA;rw [mul_sum];apply sum_congr rfl; intro i _; rw [mul_sum];apply sum_congr rfl; intro j _
     have hx': ar L K Farm.alpha =4+m :=by unfold ar stung m score; simp; omega
     rw [crit,hx',if_pos (by omega), toll, ← integral_const_mul, Nat.add_sub_cancel_left]
     apply congrArg; funext y; unfold paid layer fresco sep coreR farR activeAt alsoAt farAt stung spike c; change w y*((leg U L j [i] y*leg V K i [] y)* ((m.factorial:ℂ)⁻¹*fall (gauge m (P j)) y))=(↑m.factorial)⁻¹*_; ring
   | beta =>
     have hx': ar L K Farm.beta=4+m:=by unfold ar m stung score; simp; omega
     have hh(i j:Axis4):crit χ (coreR U V L K .beta i j) (farR W S .beta i j) (ar L K .beta) x t = c m*(∫ y:R,w y*sep m (P i) y*(leg U L j [i] y*leg V K j [] y)):=by
        rw [crit,hx',if_pos (by omega),toll,← integral_const_mul, Nat.add_sub_cancel_left]
        apply congrArg; funext y; unfold paid layer fresco sep coreR farR activeAt alsoAt farAt stung spike c; change w y*((leg U L j [i] y*leg V K j [] y)*((m.factorial:ℂ)⁻¹*fall (gauge m (P i)) y))=(↑m.factorial)⁻¹*_; ring
     simp_rw [hh,← mul_sum]; change c m * rowB P L K U V w=0; rw [sinkB,mul_zero] <;> assumption
   | delta=>
     have hx': ar L K Farm.delta=4+(m-1):=by unfold ar m stung score; simp; omega
     have hh(i j:Axis4):crit χ (coreR U V L K .delta i j) (farR W S .delta i j) (ar L K .delta) x t=c (m-1)*(∫ y:R,w y * sep (m-1) (fun l=>P j (i::l)) y*(leg U L i [] y*leg V K j [] y)):=by
        have hz: (fun l=>barrage (farR W S .delta i j) l x)=(fun l=>P j (i::l)):= funext (far_der W S i j x hx)
        rw [crit,hx',if_pos (by omega),toll,← integral_const_mul,Nat.add_sub_cancel_left]; apply congrArg;funext y; unfold paid layer fresco sep; rw [hz];change w y*((leg U L i [] y*leg V K j [] y)* ((↑(m-1).factorial:ℂ)⁻¹* _))= (↑(m-1).factorial:ℂ)⁻¹*_; ring
     simp_rw [hh,← mul_sum]
     change _ * rowC P L K U V w=0; rw [sinkC, mul_zero]
     all_goals assumption
-- COMPLETE continuum first-order integration amplitude for individual two from first, one
-- from second V3 diagrams at arbitrary marks separation. `gala` corresponds x = second mark
-- minus first (in R). Orientation signs from curls & color multiply outside all summations &
-- don't depend on i,j (color same at vertex). Different legs axis derivatives DID depend on i,j
-- and were included. Any slots (gauge-invariant) factored into this classification and spectator wires
-- at engineering count get same result; no claim discharging gauge-Ward on normalized Taylor subtractions here.
def gala (U V W:Foil)(L K S:Poke)(χ:R→ℂ)(θ:Farm)(x:R):ℂ:=∑ i:Axis4,∑ j:Axis4,
   frosted χ (coreR U V L K θ i j) (farR W S θ i j) (ar L K θ) (af S θ) x

lemma gala_abs (hχ:Base χ)(hz:z≠0): Integrable (flakes χ (coreR U V L K θ i j) (farR W S θ i j) (ar L K θ) (af S θ) z):=lively z hχ (ranchA ..) (ranchB ..) hz (by unfold ar;omega) (by unfold af;omega)
theorem fiesta (hχ:Base χ)(hz:z≠0)(hU:anti U)(hV:anti V)(hW:anti W): Waive (profile L K S) (Gap z (profile L K S) (gala U V W L K S χ θ)):=by
   let A(b:Axis4×Axis4):=coreR U V L K θ b.1 b.2;let B(p:Axis4×Axis4):=farR W S θ p.1 p.2; let a:=ar L K θ;let b:=af S θ
   have hv : b+a-4=profile L K S:=by cases θ <;> simp only [profile,b,af,a,ar,stung,spike, List.length_cons,List.length_nil] <;> omega
   have he(t:ℝ)(ht:0<t)(x:R)(p:Axis4×Axis4):crit χ (B p) (A p) b x t=0:=by
     have hw:b=(spike θ p.1).length+S.length+3:=by cases θ <;> simp only [b,af,spike,List.length_nil,List.length_cons] <;>omega
     rw [hw]; exact shave1 W S χ (spike θ p.1) (farAt θ p.1 p.2) (A p) x t hχ ht
   have hh(x:R):∑ p:Axis4×Axis4,frosted χ (A p) (B p) a b x=gala U V W L K S χ θ x:=by rw [Fintype.sum_prod_type]; rfl
   have hi:=pile z hχ (s:=Finset.univ) (A:=A) (B:=B) (a:=a) (b:=b) (fun _ _=>ranchA ..) (fun _ _=>ranchB ..) (by unfold a ar;omega) (by unfold b af;omega) hz (fun t ht=>by
      rw [Fintype.sum_prod_type]; exact shave2 U V W L K S χ θ (-z) (neg_ne_zero.mpr hz) t hχ ht hU hV hW)
     (fun t ht=> sum_eq_zero fun i _=> he t ht z i)
   simp_rw [Nat.add_comm a b,hv] at hi
   exact hi.congr fun t _=>by unfold Gap; simp_rw [hh]
end YM.RG12.Strike
