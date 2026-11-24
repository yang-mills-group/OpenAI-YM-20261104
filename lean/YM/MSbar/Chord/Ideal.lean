import YM.MSbar.Chord.Totals
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset Work.F03 Next.Free Finset
variable {G:Gauge}{n:Side}{a D C Λ:ℝ}
local notation "S₀"=> Site n
local notation "X"=> Positions (Primary n G)
local notation "N"=> (n.val:ℝ)
local notation "Θ"=>G.Color
local notation "H"=> tint G (Exterior.Body 1 n)
local notation "ι"=>G.ColorIndex
variable (e:G.Color)(R:PathData G)(q:Clip)(hp:R.Bounds q a C Λ) (s: Signed) (p:ℕ) (hr:10*(p+4)<n.val) (hE:‖e‖=1)
noncomputable def rows (A:Atom G 2) : Θ→ₗ[ℝ]Θ→ₗ[ℝ]ℝ:= by
    let F(x y:Θ):= ∑ b,A.coeff b*x (b 0)*y (b 1)
    let K(x:Θ):Θ →ₗ[ℝ]ℝ:= {
        toFun := F x
        map_add' u v:=by unfold F; simp_rw [PiLp.add_apply,mul_add,sum_add_distrib]; -- type
        map_smul' r y:=by unfold F; rw [smul_eq_mul,mul_sum]; refine sum_congr rfl (fun b _=>?_); rw [PiLp.smul_apply]; change _ * (r*_)=r*_; ring }
    exact { toFun:= K
            map_add':=fun x y=> LinearMap.ext fun z=> by change F (x+y) _=F x _+ F y _; unfold F; simp_rw [PiLp.add_apply, mul_add,add_mul,sum_add_distrib]
            map_smul':=fun r x=> LinearMap.ext fun z=> by change F (r•x) z=r*F x z; unfold F; rw [mul_sum]; refine sum_congr rfl (fun b _=>?_); rw [PiLp.smul_apply]; change _* (r *_) * _=_; ring }
lemma price_row (A:Atom G 2) (x y :Θ) : |rows A x y| ≤ A.magnitude*‖x‖*‖y‖:=by
    unfold Atom.magnitude; rw [sum_mul,sum_mul]; apply le_trans (Finset.abs_sum_le_sum_abs (s:=univ) (f:=fun b=> A.coeff b*x (b 0)*y (b 1))); apply sum_le_sum; intro i _; simp_rw [abs_mul]; exact mul_le_mul ((mul_le_mul_of_nonneg_left (show |x (i 0)| ≤ ‖x‖ from PiLp.norm_apply_le x (i 0)) (abs_nonneg _))) (show |y (i 1)|≤_ from PiLp.norm_apply_le y (i 1)) (abs_nonneg _) (by positivity)
lemma cap_row (A:Atom G 2) (x: Fin 2→Θ):A.poly x=rows A (x 0) (x 1):=by apply Finset.sum_congr rfl; intro i _; change _*(∏ i',_)= _; rw [Fin.prod_univ_two]; ring
noncomputable def readG (A:Atom G 2) (s:Signed)(i:Site n) (x y:Positions (Primary n G)) := rows A (basin s (slotFace (A.leg 0) i) x) (basin s (slotFace (A.leg 1) i) y)
include hp
lemma sunny (s:Signed)(i:Site n) (x y:X): Summable (fun k:ℕ=>readG (R.loop k) s i x y):=by
    let b(x:X):=∑ j:Face (Per n), ‖curlX s j x‖; have hb(x:X): 0≤ b x:=sum_nonneg fun _ _=>norm_nonneg _; apply Summable.of_norm_bounded (g:=fun i=>(R.loop i).budget a*b x*b y) ((hp.two.2.1.mul_right _).mul_right _); intro i
    have hv (p:Face (Per n))(x:X): ‖basin s p x‖ ≤ b x:=single_le_sum (f:=fun p=>‖curlX s p x‖) (fun _ _=>norm_nonneg _) (mem_univ _)
    refine (price_row ..).trans (mul_le_mul (mul_le_mul ((R.loop i).lower_budget _ hp.width) (hv ..) (norm_nonneg _) (hp.two.1 i)) (hv ..) (norm_nonneg _) (mul_nonneg (hp.two.1 _) (hb _)))
noncomputable abbrev liveLoop (n:Side)(R:PathData G)(x:Positions (Primary n G)) := loop R (represent ((tint G _) x))
noncomputable def era (n:Side)(R:PathData G)(x y:Positions (Primary n G)):= Patch.average (fun s:Signed=>∑ i:Site n,∑' k:ℕ,readG (R.loop k) s i x y)
lemma eraP (x y:Positions (Primary n G)) :
     let F := liveLoop n R
     Premier F ∧ rim F x y = era n R x y + era n R y x:=by
    intro F; have he:ContDiffAt ℝ ω F 0:=by
        have hv(f:Signed)(e:Edge (Site n)) : ContDiffAt ℝ ω (fun z:X=> G.mat (pull f 0 (represent (H z)) e)) 0:=by
           unfold pull Step.read; split; next h=> exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ ((represent_smooth ..).contDiffAt.comp _ (tint G (Exterior.Body 1 n)).contDiff.contDiffAt)
           exact ((represent_smooth ..).contDiffAt.comp _ (tint G (Exterior.Body 1 n)).contDiff.contDiffAt)
        unfold F liveLoop loop Patch.average; exact ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _=> Work.F02.uncut_contDiffAt hp.width hp.two (hv i))
    have hh(z:X): Tendsto (fun t:ℝ=> F (t•z)/t^2) (𝓝[≠] 0) (𝓝 (era n R z z)) :=by
        unfold F liveLoop; unfold loop Patch.average era; simp_rw [mul_div_assoc, map_smul, represent_pulled]; simp_rw [Finset.sum_div]; apply Tendsto.const_mul _ (tendsto_finsetSum _ _); intro s _; have hh:= atoms_limit (Bid.pulled (H z) s) R.loop hp.width hp.two; simp_rw [cap_row] at hh; exact hh
    obtain ⟨hz,h₀,hE⟩:= tendQ F (he.of_le le_top) _ hh; refine ⟨⟨he,hz,h₀⟩,?_⟩
    let Q:=rim F; have h2(x:X): Q x x=2*era n R x x:=by have he:=hE x; rw [iteratedFDeriv_two_apply] at he; exact he
    let K:=era n R; have hs: K (x+y) (x+y)=K x x+K x y+K y x+K y y:=by
        unfold K era Patch.average; simp_rw [←mul_add,← sum_add_distrib]; apply congr_arg; apply sum_congr rfl; intro s _; apply sum_congr rfl; intro i _; have he(x y:X):=sunny R q hp s i x y; rw [← Summable.tsum_add (he x x) (he x y),← Summable.tsum_add ((he x x).add (he x y)) (he y x),← Summable.tsum_add (((he x x).add (he x y)).add (he y x)) (he y y)]; refine tsum_congr fun j=>?_; unfold readG; simp; ring
    have hx:= h2 (x+y); rw [show era n R (x+y) _ =_ from hs,map_add,map_add,_root_.add_apply,_root_.add_apply,h2,h2,show Q y x=Q x y from he.isSymmSndFDerivAt_of_omega _ _] at hx; change Q x y= K x y+K y x; linarith only [hx]
end YM.MSbar.Midpoint
