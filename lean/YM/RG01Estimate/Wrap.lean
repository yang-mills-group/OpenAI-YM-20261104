import YM.RG01Estimate.Locator
import YM.Pert.Kinetic.Densities
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor
open Function Filter Set Lattice Wilson RG AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X:Support n}{a:Listing G n}{v:Collection.Source G n}
    (g:G.Simple) {f:Pot G n}

-- min width for padding; minimize over `expand` wrap, compare using p.B for underlying query
-- (Recovery stamp). Need existence; n size explicit.
def Leftless (n:Side)(a : RegularAddress n):= ¬ Nonwrapping (expand a) a.site
lemma remote (hn:20<n.val): ∃ a, Leftless n a:= by
    let a: RegularAddress n:= ⟨0,Finset.univ,Finset.mem_univ _⟩
    refine ⟨a,fun hh=>?_⟩
    let k:= n.val/4
    let x:Cover:=fun _=> (k:ℤ)
    have ht: lift (wrap n x) = x:= lift_eq_iff.mpr ⟨rfl,fun i=>by dsimp only [x,k]; omega⟩
    have he: k ≤ separation (wrap n x) 0:= by
       rw [separation,sub_zero, pdist, ht]
       exact (Int.natAbs_natCast _).symm.trans_le (Finset.le_sup (f:= fun i=> (x i).natAbs) (b:=(0:Axis)) (Finset.mem_univ _))
    have hx : 10*separation (wrap n x) 0<n.val:= hh _ (Finset.mem_union_left _ (Finset.mem_univ _)); unfold k at *; omega

open scoped Classical in
def coin (p:BudgetPoint)(n:Side)(hn:20<n.val) : ℕ := Nat.find (p:=fun k=> ∃ a: RegularAddress n, Leftless n a ∧ coverNumber p.B a.support=k) (by obtain ⟨a,H⟩:= remote hn; exact ⟨_,a,H,rfl⟩)
lemma left_min (p:BudgetPoint)(n:Side)(hn:20<n.val) : ∃ a, Leftless n a ∧ coverNumber p.B a.support=coin p n hn:= by unfold coin; exact Nat.find_spec (p:=fun k=>∃ a, Leftless n a ∧ coverNumber p.B a.support=k) _
lemma left_le (p:BudgetPoint)(n:Side)(hn:20<n.val)(a)(h:Leftless n a) : coin p n hn ≤ coverNumber p.B a.support:=Nat.find_min' _ ⟨a,h,rfl⟩

include g
def huge (n:Side) : ℝ := (n.val:ℝ)^2 * 3 * (Fintype.card (Site n):ℝ)^(2:ℕ)
lemma sample (x o : Site n) : p.dirBound o (p.threshold • needle G x) := by
   intro e; rw [Pi.smul_apply, needle]; have hp:= p.threshold_pos
   split
   · rw [norm_smul,spike_norm g,mul_one,Real.norm_of_nonneg hp.le]; exact le_mul_of_one_le_right hp.le (one_le_pow₀ (by simp))
   simp; positivity
lemma stab {u:ℝ}{a:RegularAddress n}(h:p.Regular a.support f)(hp:p.supBounds a.site a.support f u) (x y:Site n) : |wires f x y| ≤ u * (3/p.threshold^2):= by
   have hT:p.threshold ≠ 0:= p.threshold_pos.ne';
   have hu:= Pert.Kinetic.scaled_price g h hp (needle G x) (needle G y) (r:=1) (t:=1) zero_lt_one zero_lt_one
     (by simpa using! (sample (p:=p) g x a.site)) (by simpa using! (sample (p:=p) g y a.site))
   exact hu.trans (le_of_eq (by ring))
lemma price_home {u:ℝ}{a:RegularAddress n}(h:p.Regular a.support f)(hp:p.supBounds a.site a.support f u) : ‖judge f‖ ≤ p.threshold⁻¹^2 * huge n*u:=by
    unfold judge; rw [norm_mul,norm_neg]; calc
    _ ≤ ‖∑ x:Site n,∑ y:Site n,pitch x y^2 * wires f x y‖ := mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
    _ ≤ (∑ _x:Site n,∑ _y:Site n,(n.val:ℝ)^2 * (u*(3/p.threshold^2))) := by
      refine (norm_sum_le ..).trans (Finset.sum_le_sum fun x _=>(norm_sum_le ..).trans (Finset.sum_le_sum fun y _=>?_))
      rw [norm_mul,Real.norm_eq_abs,abs_pow]; exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (limited x y) 2) (stab g h hp x y) (norm_nonneg _) (sq_nonneg _)
    _ = _ := by unfold huge; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring_nf

lemma jury_pays {u H :ℝ}(H':Local a p v H u) (hn:20<n.val) :
    Real.exp ((p.supportExponent+3) * (coin p n hn:ℝ)) * (p.threshold^2 * ‖delta (a.read v) * (Fintype.card (Site n):ℝ)- ∑' i:ℕ,judge (v.logRead i)‖) ≤
         huge n * ((Fintype.card (Site n):ℝ)*H):= by
   let S i:= projection (a.reg i) (v.logRead i) axes01 axes01
   have hQ : delta (a.read v) * (Fintype.card (Site n):ℝ)=∑' i:ℕ, S i:= by
      have hx i:S i = ∑ o:Site n,censusAt (a.read v) o axes01 axes01 i:= by simp [Listing.read,censusAt,S]
      rw [funext hx,Summable.tsum_finsetSum (fun o _=> H'.projects.seriesAt g axes01 axes01 o)]
      change _=∑ o:Site n,total (a.read v) o axes01 axes01; simp only [isotropic g H'.projects (by omega) _ H'.transforms,ite_true,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
   rw [hQ]; let W:= Real.exp ((p.supportExponent+3)*(coin p n hn:ℝ))
   obtain ⟨b,hb,h⟩:= H'.cheap
   let z i:= b i * Real.exp ((p.supportExponent+3)*(coverNumber p.B (a.reg i).support:ℝ))
   let c (o:Site n) i:= if (a.reg i).site=o then z i else 0
   have hh (o:Site n): SumBudget (c o) H:= by
       exact h o
   have hZ i : z i = ∑ o:Site n, c o i:= by simp [c]
   have hz : Summable z ∧ (∑' i,z i) ≤ Fintype.card (Site n)*H:= by
     rw [funext hZ]; constructor; · exact summable_sum (fun o _=> (hh o).2.1)
     rw [Summable.tsum_finsetSum (fun o _=> (hh o).2.1)]
     exact (Finset.sum_le_sum (s:=Finset.univ) (fun o _=>(hh o).2.2)).trans_eq (by simp)
   let u i:= W*p.threshold^2*(S i-judge (v.logRead i))
   have hH:0≤huge n:=by unfold huge; positivity
   have hw:0≤W:= Real.exp_nonneg _
   have hk i : ‖u i‖ ≤ huge n*z i:= by
      by_cases he: Nonwrapping (expand (a.reg i)) (a.reg i).site
      · rw [show u i=0 from (by dsimp only [u,S,projection]; rw [if_pos he,catches g (H'.smooth i) (fun x hx=> he x (Finset.mem_union_left _ hx)) (by omega)]; ring), norm_zero]
        unfold z; exact mul_nonneg hH (mul_nonneg (hb i).1 (Real.exp_nonneg _))
      have hp:= price_home g (a:=a.reg i) (H'.smooth i) (hb i); have h':W≤ Real.exp ((p.supportExponent+3)*coverNumber p.B (a.reg i).support):=
        Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast (left_le p n hn (a.reg i) he)) (by linarith only [p.exponent_pos]))
      have ht:= p.threshold_pos; have hL:=hb i |>.1
      unfold u S projection; rw [if_neg he,zero_sub,norm_mul,norm_neg,Real.norm_of_nonneg (by positivity : 0 ≤ W*p.threshold^2)]
      refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_right h' (sq_nonneg _)) hp (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))) (le_of_eq ?_); unfold z; field_simp
   have hu : Summable (fun i=> ‖u i‖):= Summable.of_nonneg_of_le (fun i=> norm_nonneg _) hk (hz.1.mul_left _)
   have he: Summable S:= H'.projects.series g ..
   have hs : Summable b:= by
       refine hz.1.of_nonneg_of_le (fun i=> (hb i).1) (fun i=> le_mul_of_one_le_right (hb i).1 (Real.one_le_exp (mul_nonneg (by linarith only [p.exponent_pos]) (Nat.cast_nonneg _))))
   have hf : Summable fun i=>judge (v.logRead i):= Summable.of_norm_bounded (hs.mul_left _) (fun i=> price_home g (a:=a.reg i) (H'.smooth i) (hb i))
   change W*_ ≤ _; rw [← mul_assoc]
   rw [← Real.norm_of_nonneg (r:=W*p.threshold^2) (by positivity), ← norm_mul, ← he.tsum_sub hf, ← tsum_mul_left]
   have hh:= ((norm_tsum_le_tsum_norm hu).trans ((hu.tsum_le_tsum hk (hz.1.mul_left _))))
   exact hh.trans (by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hz.2 hH)
end YM.RG01Estimate.Censor
