import YM.LocalLTE.River.Move
/-! Maintaining bills when coloring and collecting a probe.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.River
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox FrameBox.Hall AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom Motion
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n κ:Side}{p:BudgetPoint}{d:ℕ}{F:Labels.Frame G d}{A:Hol G}{D:SectionData F}{R:Rep G n}{k v a u u' s t e x y z:ℝ}{m ℓ j:ℕ}{i:Site n}
local notation "Xp"=> Config G n→ℂ
open Next.Foundations Push.AbsoluteSums Animals
variable {L:Support n}{P Q:Coefficient F n}
variable {f:Config G n→ℂ} (c:ℂ)
lemma paints (h:Canvas D k ℓ m p L f t):Canvas D k ℓ m p L (c • f) (‖c‖*t):=by
    refine ⟨bound_smul c h.value, fun hx=>?_⟩; obtain ⟨hX,g,hg,hB,⟨v,hV,hf⟩,t',ht,X,hQ⟩:= h.analytic fun hn=> hx (by rw [hn,smul_zero])
    refine ⟨hX,c • g, regular_smul c hg, bound_smul _ hB,⟨c • v,?_,?_⟩,t',ht,X,fun b=>?_⟩
    · rw [Size.smul]; exact mul_le_mul_of_nonneg_left hV (norm_nonneg _)
    · rw [hf,smul_add,map_smul]
    let tA(i:Bool):= Port.scaleQ i ∘ g; have hh:(Port.scaleQ b)∘(c • g) = Port.scaleQ b c • (tA false)+Port.scaleQ b (c*Complex.I) • (tA true):=by
       funext U; cases b <;>simp [tA,Port.scaleQ,Complex.mul_re,Complex.mul_im]<;>ring
    rw [hh]; exact rp_add X (rp_scale X _ (hQ _)) (rp_scale X _ (hQ _))
local notation "Ω" P=> Extra.Histories.stretch c P
lemma dollar (h:Patrons D k ℓ m p P t):Patrons D k ℓ m p (Ω P) (‖c‖*t):=by
    obtain ⟨hp,⟨u,hV,hs⟩,hF⟩:= h
    refine ⟨Eq.trans_le (Size.smul F c P.x) (mul_le_mul_of_nonneg_left hp (norm_nonneg _)), ⟨(fun i=> ‖c‖*u i), ?_, fun i=> paints c (hs i)⟩, ?_⟩
    · change SumBudget (fun i=> p.mass (P.support i) _) _; simp_rw [Extra.Histories.mass_scale]; exact Local.sumBudget_mul_left hV (norm_nonneg _)
    unfold Extra.Histories.stretch; rw [hF]; simp only [smul_zero]
lemma tintV (h:Tab P 0 R k t s):Tab (Ω P) 0 R k (‖c‖*t) (‖c‖*s):=by -- YM.MergeProof.North.Shasta analogue
    obtain ⟨a,ha,hp⟩:= h.regular; obtain ⟨b,hb,hq⟩:=h.forced
    refine ⟨h.divisor,mul_nonneg (norm_nonneg _) h.first,mul_nonneg (norm_nonneg _) h.second,⟨(fun i=> ‖c‖*a i),?_, fun i=> bound_smul c (hp i)⟩, (fun i=> ‖c‖*b i),?_,fun i=> ⟨mul_nonneg (norm_nonneg _) (hq i|>.1),fun U=> (norm_smul c (P.forced i U)).trans_le (mul_le_mul_of_nonneg_left ((hq i).2 U) (norm_nonneg _))⟩⟩
    · simp_rw [Extra.Histories.mass_scale]; exact Local.sumBudget_mul_left ha (norm_nonneg _)
    simp_rw [Extra.Histories.mass_scale,mul_left_comm k ‖c‖ s]; exact Local.sumBudget_mul_left hb (norm_nonneg _)
lemma Exhibition.buckets (h:Exhibition D k ℓ m A R P Q s t e): Exhibition D k ℓ m A R (Ω P) (Ω Q) s (‖c‖*t) (‖c‖*e):=by
    have hx : decrement (Ω P) (Ω Q)= Ω (decrement P Q):=by simp [Extra.Histories.stretch,decrement,smul_sub]
    refine ⟨dollar c h.stock, stretch_format c h.format, h.layout, hx.symm ▸ stretch_format c h.trade,hx.symm ▸ tintV c h.fee,?_⟩
    rw [hx, Extra.Histories.stretch,Size.smul]; exact mul_le_mul_of_nonneg_left h.canon (norm_nonneg c)
variable {T : Type*}[Countable T] (X:ℕ≃ T×ℕ) (P Q:T→ Coefficient F n) {v e:T→ℝ}
lemma auctions (h:∀ i,Exhibition D k ℓ m A R (P i) (Q i) s (v i) (e i))(hv:Summable v)(he:Summable e)(hs:0<s): Exhibition D k ℓ m A R (Extra.Histories.merge X P) (Extra.Histories.merge X Q) s (∑' i,v i) (∑' i,e i):=by
    let Φ i:= decrement (P i) (Q i)
    have hh i:=(h i).stock.principal
    have hF i := (h i).stock.forced
    have hp : Summable fun i=> F.coeffSize (Q i).x:= hv.of_nonneg_of_le (fun i=> Work.G08.size_nonneg ..) hh
    have hp': Summable fun i=> F.coeffSize (P i).x:= (hv.add he).of_nonneg_of_le (fun i=> Work.G08.size_nonneg ..) (fun i=> (h i).price)
    have hq: Summable fun i=> F.coeffSize (Φ i).x:= he.of_nonneg_of_le (fun i=> Work.G08.size_nonneg ..) (fun i=> (h i).canon)
    let α:=(Extra.Histories.merge (n:=n) (F:=F) X); let Z:= α Q; have hZ: Z.forced=0:=by funext i j; simp [Z,α,Extra.Histories.merge,hF]
    have hκ: Z.Format 0 A R:= Extra.Histories.merge_format X Q (fun i=>(h i).format)
    have ht:(decrement (α P) Z)=α Φ:=by
       unfold decrement Z α Φ; simp only [Extra.Histories.merge, decrement]; congr 1
       · exact Eq.symm ((Size.series F hp'|>.of_norm).tsum_sub (Size.series F hp|>.of_norm))
       funext i v; simp only [Pi.sub_apply,hF,Pi.zero_apply,tsum_zero,sub_zero]
    have hx : Patrons D k ℓ m R.p Z (∑' i,v i):=by
       refine ⟨(Size.bound F hp).trans (hp.tsum_le_tsum hh hv), ?_,hZ⟩; choose q hV ht using fun i=> (h i).stock.regular
       let f x:= R.p.mass ((Q (X x).1).support (X x).2) (q (X x).1 (X x).2); let g(x:T×ℕ):= R.p.mass ((Q x.1).support x.2) (q x.1 x.2); have hp :=Extra.Histories.budget_prod (f:=g) hV hv
       exact ⟨(fun i=> q (X i).1 (X i).2),⟨fun i=> hp.1 _,hp.2.1.comp_injective X.injective,(X.tsum_eq g).trans_le hp.2.2⟩,fun i=> ht _ _⟩
    have hi i:= (h i).trade; refine ⟨hx,hκ,funext fun i=> congr_fun ((h (X i).1).layout) (X i).2, ht.symm ▸ (merge_format X Φ hi), ht.symm ▸ (MergeProof.merge_tab X Φ hs (fun i=> (h i).fee) he he).1,?_⟩
    change F.coeffSize (decrement (α P) Z).x≤_; rw [ht]; exact (Size.bound F hq).trans (hq.tsum_le_tsum (fun i=> (h i).canon) he)
end YM.LocalLTE.River
