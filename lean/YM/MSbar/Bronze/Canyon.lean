import YM.MSbar.Parma.Yummy
import YM.Work.F03.Metric
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bronze
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c: Side}(F:Nesting G c)(R : PathData G)(J:Bed)(p:Clip)
local notation "Y"=>Primary c G
local notation "T"=> Measuring.chart c G
local notation "X"=> Positions (Primary c G)
local notation "Q"=> rim (collectT c R p)
open MvPolynomial AnalyticBridge.VerifiedReset Work.F03
variable (s:G.ColorIndex) {θ η C' κ Λ ε b D t:ℝ}{d m q a':ℕ}
variable (h:R.Bounds p θ C' Λ)(ht:Attached J R)(hs:Bid.Sworn J c G)(he:Floor J p c ε D)
include h ht hs he
lemma scalar (x y:X): rim (collectT c R p) x y= Bid.gaugeFiscal J (tint G _ x) (tint G _ y) :=by
    let P:= (Fintype.card Signed:ℝ); rw [rates R p h]; unfold profitH Patch.average; let B:= Bid.gaugeFiscal J (tint G _ x) (tint G _ y)
    have hp(q:Signed): (∑ i:Face (Per c), (p.direct*inner ℝ (curlX q i x) (curlX q i y)+inner ℝ (unionC q R i x) (unionC q R i y))) = B:= by rw [← show _=B from hs q _ _]; exact (Work.F03.metric_pair J h ht _ _ he).symm -- hs
    simp_rw [hp]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ _]; positivity
lemma finches (i j:Y): Q (bolt i) (bolt j)= if i.2=j.2 then (Precision.K (J.metric.acts c)) i.1 j.1 else 0:=by
    rw [scalar R J p h ht hs he]; let K':=Precision.K (J.metric.acts c); let k(i:Y)(s:G.ColorIndex):=Exterior.parts G 1 (tint G _ (bolt i)) s
    have hk(i:Y)(s:G.ColorIndex): k i s=if i.2=s then Pi.single i.1 1 else 0:=by
        cases i with|mk i j=>funext v; unfold k; change bolt (i,j) (v,s)=(if j=s then Pi.single i 1 else 0:Positions (Body 1 c)) v; by_cases hx:j=s<;>by_cases he:i=v<;>simp [he,hx,Ne.symm,bolt,Pi.single_apply]
    change (∑ s:G.ColorIndex, dotProduct (k i s) (K' *ᵥ k j s)) = _; rw [Finset.sum_eq_single j.2]
    · rw [hk,hk, if_pos rfl]; split <;> simp [K']
    intro t ht hs; rw [hk j,if_neg (Ne.symm hs)]; simp
    simp
omit h ht hs he
-- anchor raw gross arbitrary even P no symmetry. calibrated β.
variable (p':Cacao.Pot (Primary c G))
lemma quant(ha:0≤b)(hZ:∀ i:Primary c G,cog T b d p' 1 i ≤ κ)(hp:2≤d): |caliper c (sun G s) p'|≤ κ:=by
    let s':= sun G s; let P:=(Fintype.card (Site c):ℝ); let f:=clue p'; let K:=rim f; have hP :0<P:=by unfold P;positivity
    let g(i j:Site c):=K (tuner s' i) (tuner s' j)* (AnalyticBridge.VerifiedReset.coord i j 0)^2; change |P⁻¹*(∑ i:Site c,∑ j:Site c,g i j)|≤ _
    have hx(i:Site c) : |∑ j:Site c,g i j| ≤ κ:=by
        let y(i:Site c):=primary (i,1) s
        have hp(j:Site c):K (tuner s' i) (tuner s' j) = buoy f 0 [y i,y j]:=by
            rw [stream f (y i) (y j) (helm p' _|>.contDiffAt),show rope (y i)=(i,1) from curb ..,show rope (y j)=(j,1) from curb ..];rfl
        have he:= hZ (y i); rw [← scored] at he; apply le_trans _ he
        apply le_trans (Finset.abs_sum_le_sum_abs ..); let F(i j):= |buoy f 0 [i,j]| *swipe T b d [i,j]; change (∑ j:Site c, |g i j|) ≤ ∑ j:Y,F (y i) j; calc
            _ ≤ ∑ j:Site c,F (y i) (y j):=by
               unfold g; simp_rw [hp,abs_mul,abs_pow]; refine Finset.sum_le_sum fun j _=> mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
               let e:=extent (Whisk.zone T ∅ [y i,y j]); have hx: separation j i≤e:= curve (x:=T (y j)) (y:=T (y i)) (by simp [Whisk.zone]) (by simp [Whisk.zone]); have hQ :1≤ 1+(e:ℝ):=by simp
               change _≤ liftW b d e; unfold liftW; refine ((pow_le_pow_left₀ (abs_nonneg _) ((small_coord ..).trans ((show (separation j i:ℝ)≤e from by exact_mod_cast hx).trans (by linarith : (e:ℝ) ≤ 1+e))) 2).trans (pow_le_pow_right₀ hQ ‹2≤d›)).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
            _ ≤ _:= by rw [←Finset.sum_image]; apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _); intro v _ _; exact mul_nonneg (abs_nonneg _) (effect ..|>.le); intro a _ b _ h; exact congr_arg (fun i:Primary c G=> i.1.1) h -- need fix orientation.
    rw [abs_mul,abs_of_nonneg (inv_pos.mpr hP).le]; refine (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>hx i)) (inv_pos.mpr hP|>.le)).trans_eq ?_; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact inv_mul_cancel_left₀ hP.ne' _
end YM.MSbar.Bronze
