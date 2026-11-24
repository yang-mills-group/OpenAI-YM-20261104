import YM.MSbar.Heath.Sluice
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V:Config G n}{x:Site n}{R:Rep G n}{σ C T a v δ w:ℝ}
open Finset
variable (h:R.Lawful σ C T δ w)(hv:0<v)(hw:U∈calm G n v) (hp:Stab x U V) (hz:0≤R.beta)
    (hd:Decent R.clip R.p)(ht:v ≤ R.p.threshold)
local notation "foo"=>R.path.baseTerm R.clip R.p
local notation "dv"=>R.path.principal R.clip R.p R.beta
-- raw exponent stiffness only: asking TRUE-ℓ tail from principal as margin B
-- doesn't expense β even exp(loglog)^2 except from near links v².
def lowNeed (k:Clip)(B:ℕ)(C σ v:ℝ):= ((2*B+1:ℝ)^4*(k.direct*v^2/2+(C*v)^2/2)+(C*4)*(C*2)*Real.exp (-σ/2*(B:ℝ)) * (81*meter (σ/2))) * Fintype.card PlaqAxes
def ash (B:BudgetPoint)(a:Clip)(β C σ Λ v:ℝ):= β*lowNeed a B.B C σ v + RG.PathData.loopsPrice B β C Λ *(2 *Real.exp (σ*8)*(81*meter σ))
include h hv hw hp ht hd
lemma bill_p : ∑ i, foo U i - ∑ i, foo V i ≤ lowNeed R.clip R.p.B C σ v:=by
    let k:=R.p.B; let m:=R.clip.direct*v^2/2+(C*v)^2/2; let sndL (t:Site n):=if t∈halo k {x} then m else 0
    let q := C*4*(C*2)*Real.exp (-σ/2*(k:ℝ)); have hC : 0≤ C:=budget_nonneg (h.paths.three)
    have hm:0≤ m:=by unfold m; have he:=R.clip.quadratic_pos; positivity
    have hq:0≤q:=by unfold q; positivity
    let g i:=Real.exp (-(σ/2)*separation x i); have hh (i:Face (Per n)): foo U i - foo V i ≤ sndL i.1 + q*g i.1:= by
       by_cases he: i.1∈halo k {x}
       · have h₀:= faceBound hw i; have hh:=R.path.ellShell h.paths v hv i hw; have hz: foo U i ≤ m:=by
           unfold PathData.baseTerm PathData.clipped; rw [if_pos (h₀.trans ht)]; apply add_le_add
           · apply div_le_div_of_nonneg_right _ zero_le_two; apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (G.chord_nonneg _) h₀ _) R.clip.quadratic_pos.le
           split; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hh _) zero_le_two; positivity
         unfold sndL; rw [if_pos he]; linarith only [mul_nonneg hq (show 0≤g i.1 from (Real.exp_pos _).le),hz, R.path.base_nonneg R.clip R.p V i]
       unfold sndL; rw [if_neg he,zero_add]; have hz:k<separation x i.1:= lt_of_not_ge (fun hn=>he (halo_spec.mpr ⟨x, mem_singleton_self _, hn⟩)); have ht:= base_stab h.paths i hp hz hd
       apply ((le_abs_self _).trans ht).trans; unfold q g; rw [mul_assoc _ (Real.exp _) _,← Real.exp_add]; apply mul_le_mul_of_nonneg_left;
       · refine Real.exp_monotone ?_; have he: (k:ℝ) ≤ separation x i.1:=by exact_mod_cast hz.le
         linarith only [mul_le_mul_of_nonneg_left he h.paths.width.le]
       positivity
    rw [← Finset.sum_sub_distrib]; apply (Finset.sum_le_sum fun i _=> hh i).trans; unfold lowNeed
    have hF : (∑ i,sndL i)=(halo k {x}).card *m :=by
       calc
          _ = ∑ i∈halo k {x},sndL i := (Finset.sum_subset (subset_univ _) (fun i _ hi=> if_neg hi)).symm
          _ = _:=by rw [Finset.sum_congr (g:=fun _=> m) rfl (fun i hi=> if_pos hi), Finset.sum_const,nsmul_eq_mul]
    change ∑ i: Site n × PlaqAxes,_ ≤ _; rw [Fintype.sum_prod_type, Finset.sum_comm]; simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum,hF]
    rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,mul_comm _ (Fintype.card _ :ℝ)]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_left_comm q,← mul_add]; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    refine add_le_add (mul_le_mul_of_nonneg_right ?_ hm) (mul_le_mul_of_nonneg_left (radial (σ/2) (half_pos h.paths.width) _) hq)
    exact_mod_cast horizon k x
include hz
open PathData
omit hv hw ht hd in
lemma boundAtom {i:ℕ}(W:ℕ→Atom G i) (hg:SumBudget (fun i=> (W i).budget σ) a) : ∑ j:Site n, atomSeries W R.p U j -∑ j:Site n, atomSeries W R.p V j ≤ (a * R.p.threshold^i)*(2*Real.exp (σ*8)*(81*meter σ)):=by
    have hh j := atomic W R.p j hp h.paths.width hg
    rw [← Finset.sum_sub_distrib]; refine (sum_le_sum (fun j _=> (le_abs_self _).trans (hh j))).trans ?_
    rw [← mul_sum,← mul_sum]; have h':=R.p.threshold_pos; have hc : 0≤a:=budget_nonneg hg; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (radial _ h.paths.width x) (by positivity)) (by positivity)
lemma caliber : (dv U)-(dv V) ≤ ash R.p R.clip R.beta C σ T v:= by
    have h1:= bill_p h hv hw hp hd ht -- order incl? above included hz after
    have h2:= boundAtom h hp hz R.path.cubic h.paths.three
    have h3:= boundAtom h hp hz R.path.quartic h.paths.four
    have h4:= boundAtom h hp hz R.path.loop h.paths.two
    have hz:= mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) hz; unfold PathData.principal; simp_rw [Finset.sum_add_distrib]; unfold ash RG.PathData.loopsPrice; linarith only [hz,h4]
lemma average_paid : R.path.inChannels R.clip R.p R.beta U - R.path.inChannels R.clip R.p R.beta V ≤ ash R.p R.clip R.beta C σ T v:=by
    unfold PathData.inChannels; rw [←mul_sub,←sum_sub_distrib]; let c:ℝ:= Fintype.card Signed; have hi:0<c:=by unfold c; positivity
    let a:=ash R.p R.clip R.beta C σ T v; have ht(s:Signed): (dv (pull s 0 U))-(dv (pull s 0 V)) ≤ a:=caliber h hv (holds s 0 hw) (spread hp _) hz hd ht
    apply (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=>ht i)) (inv_nonneg.mpr hi.le)).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hi.ne']
end YM.MSbar.Heath
