import YM.X.Rank.Dry
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Canopy
/-!
Every sequence of relative gauges **detectably tending to identity** without fixing the
color matrix gauges has a subsequence of exact identity readings. Application of `steady`.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter MeasureTheory Matrix Maxwell Wick Maxwell.Free
open Screen Next.Rank.Normal MvPolynomial NormedSpace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius RealInnerProductSpace ContDiff
variable {G : Gauge} {A I : Type*} {P : Mat G} {ι : Type*}

variable {R:ℕ→ WickPol G→WickPol G→Prop} (h:G.Simple) (p:ι→ WickPol G)(hp:∀ i,Painted (p i) ∧ realForm (p i)=p i)
    (q:ℕ→ι→ WickPol G)
variable (hq:∀ n i, Painted (q n i) ∧ realForm (q n i)=q n i ∧ R n (p i) (q n i)) (hR:∀ n,Relation (R n))
    (ht:∀ (i:ι)(A:Sample G),Tendsto (fun n=> helps A (q n i)) atTop (𝓝 (helps A (p i))))
private lemma firstCount (V:Type*) [MetricSpace V] : FirstCountableTopology V:=inferInstance
local instance : FirstCountableTopology (Mat G):= firstCount (Mat G)
include ht h hq hR hp
lemma freezes : ∃ᶠ n:ℕ in atTop,q n=p := by
    choose X hX H using fun n=> Relation.shim (hR n) (coreColor h)
    have He (n i A) : snap (p i) (X n) A= helps A (q n i) := by
       rw [← coat_one A]; -- all occurrence?
       let T : Crew (R n):= ⟨_,_, (hq n i).2.2,(hp i).2,(hq n i).2.1,A⟩
       have he:= data_val (1:Mat G) (q n i) A (hq n i).2.1; rw [coat_one] at he; rw [coat_one]
       exact (data_val (X n) _ A (hp i|>.2)|>.symm).trans ((congr_arg (fun r:ℝ=>(r:ℂ)) (H n T)).trans he)
    obtain ⟨Y,hY,g,hg,hG⟩:= (gram_closed (G:=G)).tendsto_subseq (fun i=>show X i∈ O G from hX i)
    have hr(i:ι)(A:Sample G) := (ht i A).comp hg.tendsto_atTop
    have hV : Same p Y 1:= by
       intro i A; rw [show snap (p i) 1 A=helps A _ from (by rw [snap,coat_one])]; refine tendsto_nhds_unique ((regularity A (p i)|>.continuous.continuousAt.tendsto).comp hG) ((hr i A).congr (fun a=> ?_)); exact (He (g a) ..).symm
    let f(n):=Y.transpose * X (g n)
    have hf:Tendsto f atTop (𝓝 1):= (show Y.transpose*Y=(1:Mat G) from hY) ▸ (tendsto_const_nhds.mul hG) -- subst?
    have hA n: f n∈O G:= folds (turns hY) (hX _)
    have hM : Same p Y.transpose 1:= by
       have he := same_comp p (a:=Y) (c:=Y.transpose) hV; rw [mul_eq_one_comm.mpr hY,one_mul] at he; exact fun i A=>(he i A).symm
    have hF n i A : snap (p i) (f n) A=helps A (q (g n) i) := by
       have he:= same_comp p (c:=X (g n)) hM; rw [one_mul] at he; exact (he i A).trans (He (g n) ..)
    have hZ n: Keeps p (f n) := fun i u A=> by rw [hF,hF, Sk_ap, ← helps_invariant,(hq _ i).1 u]
    intro hc; suffices ht:∀ᶠ (i:ℕ) in atTop, False from ht.exists.elim (fun i h=> h)
    filter_upwards [hf.eventually (steady p h fun i=> (hp i).1) , hg.tendsto_atTop.eventually hc] with i he hv; apply hv
    specialize he (hA i) (hZ i); funext a; refine helps_filters _ _ (fun A=>?_); rw [← hF]; exact (he a A).trans (by rw [snap,coat_one])
end YM.PositionX.Rank
