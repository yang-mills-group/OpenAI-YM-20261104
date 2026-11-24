import YM.MSbar.Chord.Carpet
import YM.Corona.Fit
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter
open AnalyticBridge.SectorAffine.Offset
open Lattice Wilson Gauge Work.F03 Push Push.Uniform RG Precision AnalyticBridge.VerifiedReset Planned.AtomRegular MSbar.Rolling MSbar.Wave Set
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c : Side}{p:BudgetPoint}{X : Support c}{g : Config G c → ℝ} {d: RegularAddress c}{a W:ℝ}
local notation "V"=> Config G c
local notation "E₀"=> Positions (Primary c G)
variable (e:G.Color)(hG:G.Simple)
variable (h : p.Regular d.support g)
include h hG
lemma ethos (x y:Positions (Primary c G)) : rim (Program g) x y=logHessian g ((panel G c) x) ((panel G c) y):=by
    have he:= germ_diff h; have hp:= flat_critical hG h; have hD:= Work.F03.hessian_comp (f:=germ g) (map_zero ((panel G c).toContinuousLinearMap)) he ((panel G c).toContinuousLinearMap.contDiff.contDiffAt) hp|>.2 x y; rw [iteratedFDeriv_two_apply,(panel G c).toContinuousLinearMap.fderiv] at hD; exact hD
noncomputable def RimL (Q:FaceRail c G) : PMap c G := {
    toFun:=fun x=> (Q x).toLinearMap
    map_add':=fun x y=> LinearMap.ext fun z=> by change Q _ _=Q x z+Q y z; rw [map_add,_root_.add_apply]
    map_smul':=fun r x=> LinearMap.ext fun z=> by change Q (r•x) _=r • Q x z; rw [map_smul,_root_.smul_apply] }
local notation "Z"=>rim (Program g)
local notation "A"=> tuner e
lemma testerC {B:Activities G c}(hb:B.RegularFamily p)(i:ℕ)(h0:g=B.E i)(hP:B.reg i=d)(hp: Nonwrapping d.support d.site)(hx:4≤c.val) : gross (fun x y=> rim (Program g) x y) e=0 :=by
   let k:=RimL Z; let K : LinearJet G := wedge pair e; let T:= queue e c (fun x=> coord d.site x 0); have ht : panel G c T = K.field d.site:=by
        funext i; have hg:= tally e (fun i=> coord d.site i 0) i.1 i.2; have hh :i.fst=i.fst:=rfl; change panel G c (queue e c (fun x=> coord d.site x 0)) (i.1,i.2)=(wedge pair e).field d.site i; rw [hg,wedge_field]; simp [pair,eq_comm]
   have hg(i j : E₀): k i j=logHessian g (panel G c i) (panel G c j):= ethos hG h ..
   let z:=queue e c (fun _=>1); have hn : panel G c z = (LinearJet.field ({at0:=fun i=> if i=1 then e else 0, slope:=0} :LinearJet G) d.site) := by funext i; unfold z; obtain ⟨x,i⟩:=i; rw [tally]; simp [LinearJet.field]
   have hs : ∃ s:Site c → G.Color, Agrees d.support (panel G c z) (AnalyticBridge.VerifiedReset.gradient s) := by
        rw [hn]; obtain ⟨s,hs⟩:=LinearJet.gradient_agrees (G:=G) ({at0:=fun i=> if i=1 then e else 0, slope:=0}) hp hx (by ext; simp [LinearJet.positive,LinearJet.curl]); exact ⟨s,fun i h1 h2 => (hs i h1 h2).symm⟩
   have hb'(i:E₀): k z i=0:=by
        obtain ⟨s,hh⟩:=hs; rw [hg, hessian_agrees hG h hh (show Agrees d.support (panel G c i) (panel G c i) from fun _ _ _=>rfl),hessian_gradient hG h]
   have hF(i j:E₀):k j i=k i j:=by rw [hg,hg,hessian_symm h]
   have he(x:Site c) (y:E₀)(hc : x∉d.support) : k (A x) y=0:=by
        let i: Edge (Site c):=(x,1); rw [hg,show panel G c (A x)=Pi.single (x,1) e from edges G i e,hessian_agrees hG h (b:=(0:Directions G c)) _ (fun i _ _=> rfl)]; swap
        · intro i hi hm; exact Pi.single_eq_of_ne (fun (h:i=(x,(1:Axis)))=> hc ((show i.1=x from congr_arg Prod.fst h) ▸ hi)) ..
        rw [hessian_eq,map_zero,_root_.zero_apply]; -- wrong
   change gross (fun x y=>k x y) e=0; rw [squareX2 d.site e k]; rotate_left
   · intro x; change k z _=0∧k _ z=0; exact ⟨hb' _,(hF z _).trans (hb' _)⟩
   · intro i j hj; exact ⟨hp _ (by_contra fun hz=>hj (he i _ hz)),hp _ (by_contra fun hz=>hj ((hF _ _).trans (he j _ hz)))⟩
   rw [show k T T=0 from ?_,mul_zero]; rw [hg,ht,h0]; have h : IsAffineDirection (B.reg i).site (K.field d.site):=by rw [hP]; exact (LinearJet.isAffine _).mpr ⟨K,rfl⟩
   exact hb.vanish i (hP ▸ hp) _ _ h h
-- estimate singular with real dirs. z→.K.C.E.
variable (hE:‖e‖≤1)
include hE
lemma op_one(o:Site c):‖tuner e o‖ ≤ 1:=by
    let u:= tuner e o; have ht: panel G c u=Pi.single (o,1) e:=edges G _ _; have he(v:E₀) : ‖v‖ ≤ ‖panel G c v‖:=by
         refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> ?_
         obtain ⟨⟨x,i⟩,j⟩:= i; obtain ⟨i,rfl⟩:= Exterior.axisEquiv.surjective i; exact (PiLp.norm_apply_le (panel G c v (x,i)) j).trans (norm_le_pi_norm _ _)
    apply (he u).trans; rw [ht]; apply (pi_norm_le_iff_of_nonneg zero_le_one).2; intro i; by_cases hx:i=(o,1) <;> simp [hx]; exact hE
lemma heavyA (hy:p.supBounds d.site d.support g a) : |gross (fun x y=>rim (Program g) x y) e| ≤ (earnE p G 2*a)*size c:=by
   have he:palace (0:E₀)=1:=by unfold palace; rw [map_zero,Work.G07.at_zero_increment]
   have hb:2 ≤ p.order:= (by norm_num: 2≤ 6).trans p.order_ge
   have ht := fluxP h (d:=d) (x:=0) hy (show Healthy p.threshold d.support (palace 0) from he.symm ▸ flat_ok p d.support) hb (by norm_num) -- order
   refine hefty e _ (fun i j=>?_); let L:=iteratedFDeriv ℝ 2 (Program g) 0; let v:=![tuner e i,tuner e j]; have hw:rim (Program g) (tuner e i) (tuner e j)=L v:=by unfold L; rw [iteratedFDeriv_two_apply]; rfl
   change |rim _ _ _| ≤ _; rw [hw]; apply (ContinuousMultilinearMap.le_opNorm L v).trans; rw [Fin.prod_univ_two]; apply le_trans (mul_le_of_le_one_right (norm_nonneg _) _) (ht.pay 2 le_rfl); exact mul_le_one₀ (op_one e hG h hE i) (norm_nonneg _) (op_one e hG h hE j)
end YM.MSbar.Midpoint
