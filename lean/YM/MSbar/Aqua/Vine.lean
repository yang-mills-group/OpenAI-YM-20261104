import YM.MSbar.Aqua.Beacon
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "E"=>Positions (Primary n G)
local notation "Λ"=>Native.Chart.Rail G
variable {d a b C:ℝ}
variable (W:Rep G n)(S:Nesting G n)(r:ℝ) (c i:ℕ)
noncomputable def vine (W: Rep G n)(r:ℝ)(x:Positions (Primary n G)) := walnut W (r • x)
noncomputable def ore (W: Rep G n)(S:Nesting G n)(r:ℝ)(k:ℕ)(x:Positions (Primary n G)) := ∑ i∈Finset.range (k+1), r^i* atlas S k i W.path W.clip x
noncomputable def film (W:Rep G n)(S:Nesting G n)(r:ℝ)(k:ℕ):Positions (Primary n G)→ℝ:= vine W r- ore W S r k
lemma pure : ContDiff ℝ ω (ore W S r i):= ContDiff.sum fun j _=>ContDiff.mul contDiff_const (vent ..)
variable {F:ℝ→ Config G n→ℝ}(hp:Trend F S W.path W.clip i)
variable (h:Beam G d)(hA:Touch W.eval)
variable (x:Positions (Primary n G))(z:Site n→G.Color)
variable (hk: ∀ i:Body 1 n, ‖tint G _ (r • x) i‖<d)(hd:DifferentiableAt ℝ (vine W r) x)(hr:r≠0)
local notation "ω'"=> tariff n i W.clip W.path S
local notation "Ι"=> range (i+1)
local notation "X"=> vine W r
local notation "Q"=> film W S r i
local notation "J"=>fun u:ℕ=> atlas S i u W.path W.clip
include hp
lemma cancelP : ∑ u∈Finset.range (i+1),r^u*fderiv ℝ (atlas S i u W.path W.clip) x (Work.G05.blockTaylor (i-u) (speedsK z) (r • x))=0:=by
    let H(u j:ℕ):= fderiv ℝ (J u) x (Tensor.diagonal (Tensor.coeff (speedsK z) j 0) x); have he(u):r^u*fderiv ℝ (J u) x (Work.G05.blockTaylor (i-u) (speedsK z) (r • x))=∑ j∈ range (i-u+1),r^(u+j)* H u j:=by unfold Work.G05.blockTaylor; rw [Finset.sum_apply,map_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [Tensor.homogeneous,map_smul,smul_eq_mul]; unfold H;ring
    let A(u j:ℕ):= r^(u+j)*H u j; change (∑ u∈ Ι,r^u*fderiv ℝ (J u) x _)= _; simp_rw [he]; change ∑ u∈Ι,∑ j∈range (i-u+1), A u j=_; rw [← Wave.aims]; apply Finset.sum_eq_zero; intro j hj; have h₀ : ∑ u∈range (j+1), H u (j-u)=0:=by have hv:= ascends z W.path W.clip S i x hp j (Nat.lt_succ_iff.mp (mem_range.mp hj)); simp_rw [billFlight] at hv; exact hv
    unfold A; rw [← mul_zero (r^j),← h₀, Finset.mul_sum]; exact Finset.sum_congr rfl fun u hu=>by rw [show u+(j-u)=j by have h:= Finset.mem_range.mp hu; omega]
include h hk hd hA hr
omit hp in
lemma vineyard : fderiv ℝ (vine W r) x (speedsK z (r • x))=0:=by
    obtain ⟨hx,ht,hL⟩:= year z (r • x) h hk
    let v(t:ℝ):= r⁻¹ • (cones z (t,(r • x))); have he:v 0=x:=by unfold v; rw [hx,inv_smul_smul₀ hr]
    have hv: HasDerivAt v (r⁻¹ • (speedsK z (r • x))) 0:= ht.const_smul (r⁻¹)
    have hp : ∀ᶠ t:ℝ in 𝓝 0,X (v t)= X x:=by
        filter_upwards [hL] with t hb; unfold v vine walnut; rw [smul_inv_smul₀ hr,hb,hA.shield]
    have ht:=(show HasFDerivAt (X) (fderiv ℝ (X) x) (v 0) from (by rw [he]; exact hd.hasFDerivAt)).comp_hasDerivAt (0:ℝ) hv
    have hh:= ht.unique ((hasDerivAt_const (0:ℝ) (X x)).congr_of_eventuallyEq (by exact hp)); rw [map_smul,smul_eq_mul,mul_eq_zero] at hh; exact hh.resolve_left (inv_ne_zero hr)
lemma wants : fderiv ℝ (film W S r i) x (grad z) = -(fderiv ℝ (film W S r i) x (speedsK z (r • x)-grad z)+
        ∑ u∈Finset.range (i+1),r^u*fderiv ℝ (atlas S i u W.path W.clip) x (speedsK z (r • x)-Work.G05.blockTaylor (i-u) (speedsK z) (r • x))) :=by
    simp_rw [map_sub,mul_sub,sum_sub_distrib, cancelP W S r i hp x z]; let K:=fderiv ℝ (ore W S r i) x; let w:= speedsK z (r • x)
    have ht: fderiv ℝ Q x = fderiv ℝ X x - K := fderiv_sub hd ((pure W S r i).differentiable (by simp) x)
    have hD(u:ℕ) : HasFDerivAt (fun y=>r^u * J u y) (r^u • fderiv ℝ (J u) x) x:= ((vent (PowerSeries.coeff u ω')|>.differentiable (by simp) x).hasFDerivAt).const_smul (r^u) -- plumbing
    have hV : K w=∑ u∈Ι,r^u * fderiv ℝ (J u) x w:=by
        apply Eq.trans (congrArg (fun f:E→L[ℝ]ℝ=>f w) ((HasFDerivAt.fun_sum (u:=Ι) (fun u _=>hD u)).fderiv)); rw [_root_.sum_apply]; rfl
    rw [ht,_root_.sub_apply, _root_.sub_apply, vineyard W r h hA x z hk hd hr]; -- hk overwritten! edit.
    rw [show K _= _ from (show K (speedsK z (r • x))= ∑ u∈Ι,r^u *fderiv ℝ (atlas S i u W.path W.clip) x (speedsK z (r • x)) from hV)]; ring
end YM.MSbar.Aqua
