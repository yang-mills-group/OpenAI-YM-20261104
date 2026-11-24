import YM.MSbar.Chord.Tiles
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}{Q:FaceRail n G}{Z:ℝ}
local notation "S₀"=> Site n
local notation "E"=> Edge (Site n)
local notation "N"=> n.val
local notation "M"=> Moment Q
variable (x:Edge (Site n)) (u v:G.Color) (h:Ribbon Q)(hQ:Weigh Q Z) (hu:‖u‖=1)(hv:‖v‖=1)
-- tests using arbitrary single color.
private lemma verses (f:Directions G n) : (panel G n).symm f=∑ i: Edge (Site n), bead G i (f i) :=by
    apply (panel G n).injective; rw [map_sum]; simp_rw [edges,(panel G n).apply_symm_apply]; funext i; change f i= (∑ i:Edge (Site n),(Pi.single i (f i):Directions G n)) i; rw [Finset.sum_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]; rw [Pi.single_eq_same]; exact fun j _ h=> Pi.single_eq_of_ne h.symm ..
def sway(f:S₀→ℝ)(i:Edge (Site n)):= f (i.1+step i.2)- f i.1
include h
lemma push_pack (f:S₀→ℝ) : ∑ i : Edge (Site n), cell Q x i u v * sway f i=0:=by
    let k(j:S₀):=f j • v; have hz(i:E): gradient k i= sway f i • v:=by rw [sway,sub_smul];rfl
    rw [← show Q (bead G x u) (grad k)=0 from h.zeroG .., Wave.grad, verses, map_sum]; apply Finset.sum_congr rfl; intro i hi; rw [hz, map_smul,map_smul];exact mul_comm ..
include hQ hu hv
lemma broad {f: S₀→ℝ}{A:Edge (Site n) → ℝ}{B:ℝ}(hb:0≤B)(H:∀ i,(sway f i-A i)≠0 → N ≤100*(separation i.1 x.1 +1)∧ |sway f i-A i| ≤ B*beadPad x.1 i.1 3) :
    |∑ i:E, cell Q x i u v * A i| ≤ 4*(B*tumbler n Z):=by
    let e:E→ℝ:=fun i=>cell Q x i u v; let g(i:E):=sway f i -A i; let d:=B*tumbler n Z
    have hh(c:Axis):|∑ i:S₀,e (i,c)*g (i,c)|≤d:=values x c u v _ hQ hu hv hb (fun i=> H (i,c))
    rw [show ∑ i:E,cell Q x i u v*A i= -(∑ i:E,e i*g i) from ?_,abs_neg]; swap; · unfold g; simp only [mul_sub,Finset.sum_sub_distrib];rw [show ∑ i:E,e i*sway f i=0 from push_pack x u v h f]; abel
    rw [Fintype.sum_prod_type, Finset.sum_comm]; exact ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (g:=fun _=>d) (fun i _=>hh i))).trans_eq (by rw [Finset.sum_const,nsmul_eq_mul]; simp [Axis,d])
omit h hQ hu hv
lemma sway_mid (i:E)(c:Axis)(hx:100*(separation i.1 x.1+1)<N) : zone x (i.1+step i.2) c = middle x i c +halfE i.2 c:=by
    unfold zone middle; unfold zone; rw [coord_step (show _<_ by omega) (by omega)]; unfold halfE; by_cases he:c=i.2<;>simp[he]<;>ring
lemma zone_low (i:E)(c:Axis) : zone x i.1 c=middle x i c-halfE i.2 c:= by unfold middle; abel
lemma sofa (v:S₀)(c:Axis): |zone x v c| ≤ beadPad x.1 v 1:= by
    unfold zone; refine (abs_sub ..).trans (le_trans (add_le_add (d:=1) (small_coord ..) ?_) ?_); · exact show |halfE x.2 c| ≤ 1 from (by unfold halfE; split <;> norm_num)
    unfold beadPad;rw [pow_one];exact add_comm ..|>.le
lemma sofB (i:E)(c:Axis):|zone x (i.1+step i.2) c| ≤ 2*beadPad x.1 i.1 1:=by
    apply (sofa ..).trans; have he: separation (i.1+step i.2) x.1 ≤ 1+separation i.1 x.1:= (separation_triangle _ i.1 _).trans (Nat.add_le_add_right ((separation_comm ..).trans_le (Work.E01.sep_step_le ..)) _)
    unfold beadPad; rw [pow_one,pow_one]; exact_mod_cast (show 1+separation (i.1+step i.2) x.1 ≤ 2*(1+separation i.1 x.1) by omega)
include h hQ hu hv
lemma homeR (c:Axis): |M x c u v []| ≤16*tumbler n Z:=by
    let g(b:E):ℝ:= if c=b.2 then 1 else 0; let f(i):=zone x i c; let W:= tumbler n Z; have hw(i:E)(ht:sway f i-g i≠0): n.val≤100*(separation i.1 x.1+1)∧|sway f i-g i|≤ 4*beadPad x.1 i.1 3:=by
       let p:=beadPad x.1 i.1 1; have hy:1 ≤ p:=by unfold p beadPad; rw [pow_one]; simp
       unfold g f at ht ⊢; constructor
       · by_contra! h; apply ht; unfold sway; dsimp only; rw [sway_mid x i c h, zone_low x i]; unfold halfE; by_cases he:c=i.2<;> simp [he]<;> ring
       refine (abs_sub ..).trans ?_; unfold sway; have hg:= (abs_sub ..).trans (add_le_add (sofB x i c) (sofa x i.1 c)); apply (add_le_add hg (show |g i| ≤ 1 from (by unfold g; split <;> norm_num))).trans; refine le_trans ?_ (mul_le_mul_of_nonneg_left (P_pad x.1 i.1 1 3 (by omega)) (by norm_num:0 ≤ (4:ℝ))); change _+p+1≤ 4*p; linarith only [hy]
    rw [show M x c u v []=∑ i:E,cell Q x i u v*g i from ?_]; swap; · unfold Moment; unfold g; rw [Fintype.sum_prod_type]; simp [mold,mul_ite]
    exact (broad x u v h hQ hu hv (by norm_num) hw).trans_eq (by ring)
end YM.MSbar.Midpoint
