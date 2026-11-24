import YM.X.Chir.Comb
/-!
# Color-free connected Θ raw measurement after φ equival. Terminal projection. large-z geometry.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open Maxwell (Green)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "S"=>Site n
local notation "L"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
local notation "T"=>Tet
local notation "o"=>side q k
local notation "D"=>Interval.mass
variable (t u v w:Tet)(X Y Z:Fielding.Walk)
-- color omitted. spin contact. 
local notation "Tτ"=> transit q
abbrev Ter:= Tet→ Tet→ Tet→ Tet→ℝ
def trion (e:ℝ)(x y z:S):ℝ:= ∑ p:T,∑ u:T,∑ v:T, Α (fun a b=>Wpp e 1 a (-1) b n z x) (fun a b=> Wpp e 1 a (-1) b n z y) p u v* (ester n e 1 p u v x y z-∑ t:T,Union_z n e x y z t u v p)
def W_union (q:ℕ+)(X Y Z:Fielding.Walk)(t u v w:T)(k:ℕ):= Union_z (side q k) (epsilon q k) (transit q X k) (transit q Y k) (transit q Z k) t u v w
def RootJ (q:ℕ+)(X Y Z:Fielding.Walk)(J:Ter):Prop:=∀ t u v w:T,Tendsto (W_union q X Y Z t u v w) atTop (𝓝 (J t u v w))
def WarpF (q:ℕ+)(X Y:Fielding.Walk)(r:ℝ)(t u v:T): Weave q:= ∑ i:Axis,∑ j:Axis, (↑(form r t i j):ℂ) • (wef q X 1 (transfer (-1) u i) * wef q Y 1 (transfer (-1) v j))
lemma warpF (w:Site (side q k))(r:ℝ): WarpF q X Y r t u v k w= ↑(ester o (ε k) r t u v (Tτ X k) (Tτ Y k) w):= by unfold WarpF ester; simp only [Finset.sum_apply, Complex.ofReal_sum,Complex.ofReal_mul,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,mul_assoc];rfl
def glow (q:ℕ+)(X:Fielding.Walk)(p u:T): Weave q:= wef q X 2 (exchangeF 1 p (-1) u)
lemma glow_val (z:Site (side q k)): glow q Z t u k z= (Wpp (ε k) 1 t (-1) u (side q k) (Tτ Z k) z:ℂ):= rfl
lemma encountered : Complex.ofReal (W_union q X Y Z t u v w k)= crow q (glow q Z w t * WarpF q X Y (-1) t u v) k:= by unfold W_union Imprint.Union_z galley crow; rw [Complex.ofReal_mul,Complex.ofReal_pow]; simp_rw [Complex.ofReal_sum,Complex.ofReal_mul,Pi.mul_apply,warpF,glow_val];rfl
variable (a:G.ColorIndex)(χ:Floor R)(H:Geom q r X Y Z)(hq:1<q.val)(hr:R<r)
include a χ H hq hr
lemma saw : Released (W_union q X Y Z t u v w):= by
    let p:=glow q Z w t; let f:=W_union q X Y Z t u v w; have h : (fun k:ℕ=> Complex.ofReal (f k)) ∈ crew:= by
         unfold f; simp_rw [encountered, WarpF]; simp_rw [Finset.mul_sum, crowd_onto]; -- parentheses under fun i result eval; careful
         -- move functions
         apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _; rw [mul_smul_comm, crowd_scale]; apply Submodule.smul_mem; apply (show Released _ from ?_); unfold glow; rw [kiteV u i X a,kiteV v j Y a,←mul_assoc]; exact lift_view a χ hq Z X Y ((H.circles q ..).circles q ..) hr _ 2 (exchange_air w t 1 (-1)) (by norm_num) _ _ _ _
    obtain ⟨m,hm⟩:= (show Released _ from h); exact ⟨m.re, Complex.continuous_re.continuousAt.tendsto.comp hm⟩
lemma encounter : ∃ J:Ter, RootJ q X Y Z J:= by choose f hf using fun t u v w=> saw t u v w X Y Z a χ H hq hr; exact ⟨_,hf⟩
omit a χ H hq hr
variable {x y z:E4}
def seedL (x y z: E4)(p u v:T):=∑ i:Axis,∑ j:Axis, form 1 p i j* Cup u i (x-z)*Cup v j (y-z)
def SpinLimit (J:Ter)(x y z:E4):= ∑ i:T,∑ u:T,∑ v:T, Α (solar (z-x)) (solar (z-y)) i u v*(seedL x y z i u v - ∑ p:T,J p u v i)
lemma a_limit (f g:ℕ→Arena)(F G:Arena)(hf:∀ a b:T, Tendsto (fun k=> f k a b) L (𝓝 (F a b)))(hg:∀ a b:T,Tendsto (fun k=>g k a b) L (𝓝 (G a b))): Tendsto (fun k=>Α (f k) (g k) t u v) L (𝓝 (Α F G t u v)):= ((hf (loop t) _).mul (hg ..)).sub ((hf ..).mul (hg ..))
include hq
variable (hz:x≠z)(ht:y≠z)(hxy:x≠y) (hx:plot q X x)(hy:plot q Y y)(hX:plot q Z z)
include hx hy hX hz ht
lemma seed_limit : Tendsto (fun k=> ester (side q k) (ε k) 1 t u v (Tτ X k) (Tτ Y k) (Tτ Z k)) L (𝓝 (seedL x y z t u v)):= tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ fun j _=> ((urn u i _ _ hz hx hX hq).const_mul _).mul (urn v j _ _ ht hy hX hq))
lemma spin_limit (J:Ter)(hp:RootJ q X Y Z J): Tendsto (fun k=>trion (ε k) (Tτ X k) (Tτ Y k) (Tτ Z k)) L (𝓝 (SpinLimit J x y z)):= by
    unfold trion SpinLimit; refine tendsto_finsetSum _ (fun t _=> tendsto_finsetSum _ fun u _=> tendsto_finsetSum _ fun v _=> Tendsto.mul ?_ (Tendsto.sub ?_ ?_)); · exact a_limit t u v _ _ _ _ (fun i j=> turbine hq hz.symm hX hx i j) (fun i j=> turbine hq ht.symm hX hy i j);
    · exact seed_limit t u v X Y Z hq hz ht hx hy hX
    exact tendsto_finsetSum _ (fun i _=>hp i _ _ _)
end YM.PositionX.Chir
