import YM.MSbar.Chord.Tow
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter
open AnalyticBridge.SectorAffine.Offset
open Lattice Wilson Gauge Work.F03 Push Push.Uniform RG Precision AnalyticBridge.VerifiedReset Planned.AtomRegular MSbar.Rolling MSbar.Wave Set
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c : Side}{p:BudgetPoint}{X : Support c}{g : Config G c→ℝ} {d:RegularAddress c}{a W r K Λ σ:ℝ}
local notation "V"=> Config G c
local notation "E₀"=> Positions (Primary c G)
variable {A:Activities G c}(h:A.Valid p a W){S:Set (Positions (Primary c G))}
def Bash (S : Set (Positions (Primary c G)))(p:BudgetPoint): Prop:= ∀ x∈S,‖x‖≤1∧ RG.flags p.threshold (palace x)=∅
noncomputable def arc (A:Activities G c)(p: BudgetPoint): Positions (Primary c G)→ℝ:= Program (A.additive p)
variable (hx:IsOpen S)(hc:Convex ℝ S)(hs:Bash S p)
include h hx hc hs
lemma heir (x)(hm:x∈S) (n:ℕ)(hn:n≤ p.order): ContDiffAt ℝ n (arc A p) x ∧ ∀ k,k≤n → HasSum (fun i=> iteratedFDeriv ℝ k (Program (A.E i)) x) (iteratedFDeriv ℝ k (arc A p) x):=by
    obtain ⟨C,hC,H⟩:= A.E_total h.boundE; let F i (v:E₀):= Program (A.E i) v; let V':=earnE p G n; have hp(i)(p')(hr:p'∈ S) : Through n (F i) p' (V'*C i):=fluxP (h.regular.smooth i) (H i) (show Healthy p.threshold (A.reg i).support (palace p') from (by unfold Healthy; rw [(hs p' hr).2]; simp)) hn (hs p' hr|>.1)
    have ht : (arc A p) =ᶠ[𝓝 x] (fun y=> ∑' i,F i y):=by
        filter_upwards [hx.mem_nhds hm] with y hy; unfold arc; apply tsum_congr; intro j; exact masked_eq _ _ _ _ (by unfold Healthy; rw [(hs y hy).2];simp)
    refine ⟨(topS hx hc hp (hC.mul_left _) x hm).smooth.congr_of_eventuallyEq ht,fun k hk=>?_⟩; rw [(ht.iteratedFDeriv ℝ k).eq_of_nhds]; exact will hx hc hp (hC.mul_left _) hk x hm
local notation "N"=> c.val
local notation "η"=> p.supportExponent
noncomputable def brim (c:Side)(p:BudgetPoint)(G:Gauge) (m:ℕ) := earnE p G 2 *size c *Real.exp (-p.supportExponent*m)
noncomputable def sing (A:Activities G c)(i:ℕ)(e:G.Color) := gross (fun x y=> rim (Program (A.E i)) x y) e
variable (e:G.Color)(he:‖e‖≤1)(hG:G.Simple)(hm:(0:Positions (Primary c G)) ∈S)
include he hm hG
lemma deposit (u v:ℕ)(hp:p.B ≤ v)(hr:10*(u*(4*v+2)+2*v) < c.val)(hn:4 ≤ c.val) : |grossH (rim (arc A p)) e| ≤ brim c p G u*a:=by
    let Y:= brim c p G u; have ht:= heir h hx hc hs _ hm 2 ((by norm_num: 2 ≤ 6).trans p.order_ge); let G'(i:ℕ)(x y:Positions (Primary c G)):= rim (Program (A.E i)) x y; have hh(x y): HasSum (fun i=> G' i x y) (rim (arc A p) x y):=by
        let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2=> Positions (Primary c G)) ℝ ![x,y]
        have H := L.hasSum (ht.2 2 le_rfl); change HasSum _ (iteratedFDeriv ℝ 2 (arc A p) 0 _) at H; rw [iteratedFDeriv_two_apply] at H; apply H.congr_fun; intro i; symm; change (iteratedFDeriv ℝ 2 (Program (A.E i)) 0) _ = _; rw [iteratedFDeriv_two_apply]; rfl -- wrong `HasSum.congr_fun` orientation
    have hT: gross (fun x y=>rim (arc A p) x y) e=∑' i,sing A i e:=by
        simp_rw [← fun x y=> (hh x y).tsum_eq]; exact mosaic _ _ (fun i j=> (hh _ _).summable)|>.2
    obtain ⟨b,hB,hz⟩:=h.boundE; let F(x:Site c)(i:ℕ):= if (A.reg i).site=x then p.mass (A.reg i).support (b i) else 0; let f(i:ℕ):= Y*∑ x,F x i; have hY:0 ≤ Y:=by have hh:= floorP G p 2; unfold Y brim size; positivity
    have hF(i:ℕ): |sing A i e| ≤ f i:=by
       let M:= p.mass (A.reg i).support (b i); let r:= A.reg i
       have hM:f i=Y*M:=by unfold f F M;simp
       rw [hM]; by_cases ht:Nonwrapping r.support r.site
       · rw [sing,testerC (d:=r) e hG (h.regular.smooth i) h.regular i rfl rfl ht hn,abs_zero]; exact mul_nonneg hY ((hB i).1.trans (p.loMass r.support (b i) (hB i).1))
       have h₀ := heavyA (d:=r) e hG (h.regular.smooth i) he (hB i); let B:=coverNumber p.B r.support; have h : u<B :=by
           by_contra! hz; apply ht; intro k hk; have hp : separation k r.site≤ (u*(4*v+2)+2*v):=(Corona.extent r.support p.B hk r.anchor).trans (Nat.add_le_add (Nat.mul_le_mul hz (by omega)) (by omega)); omega
       have ha: Real.exp (-η*u)* Real.exp (η*B) ≥ 1:=by rw [←Real.exp_add]; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left (show (u:ℝ)≤ B from by exact_mod_cast h.le) p.exponent_pos.le]; -- hp shadow
       apply h₀.trans <| le_trans _ (le_refl (Y*M)); unfold Y M brim BudgetPoint.mass; let T:=earnE p G 2*(b i)*size c
       calc _ ≤ T*(Real.exp (-η*u)*Real.exp (η*B)):=le_mul_of_one_le_right (mul_nonneg (mul_nonneg (floorP G p 2) (hB i).1) (by unfold size; positivity)) ha
            _ = _:=by unfold T B r; ring
    let A':= fun i=>sing A i e; have hs:Summable (fun i=>∑ x,F x i):=summable_sum fun i _=> (hz i).2.1; have hu:= hs.mul_left Y; have hi := hu.of_nonneg_of_le (fun i=> norm_nonneg (A' i)) hF
    unfold grossH; rw [hT, abs_mul, abs_of_nonneg (by positivity : 0≤ (Fintype.card (Site c):ℝ)⁻¹)]; let C':=(Fintype.card (Site c):ℝ); have hh:0 < C':= by unfold C'; positivity
    refine (mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hi).trans (hi.tsum_le_tsum hF hu)) (inv_pos.mpr hh|>.le)).trans ?_; rw [tsum_mul_left,Summable.tsum_finsetSum (fun i _=> (hz i).2.1)]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (g:=fun _=>a) (fun i _=>(hz i).2.2)) hY) (inv_pos.mpr hh|>.le)).trans_eq ?_; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; change C'⁻¹*(Y*(C'*a))=_; change _=Y*a; field_simp
end YM.MSbar.Midpoint
