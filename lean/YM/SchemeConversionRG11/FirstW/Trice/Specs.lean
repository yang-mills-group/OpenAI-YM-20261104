import YM.SchemeConversionRG11.FirstW.Trice.Spark
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{u:∀ i,Full.Grid (T.period i) 3}{p:Nodes} {n:Side}
-- Zenith overlap
private lemma S34 {A B: Type*}[Fintype A][Fintype B](f:A→A→A→B→B→B→B→ ℂ) : (∑ a,∑ b,∑ c,∑ d,∑ e,∑ j,∑ k,f a b c d e j k)=∑ d,∑ e,∑ j,∑ k,∑ a,∑ b,∑ c,f a b c d e j k := by
 simpa only [Fintype.sum_prod_type] using Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun i:A×A×A=> fun j:B×B×B×B=>f i.1 i.2.1 i.2.2 j.1 j.2.1 j.2.2.1 j.2.2.2)
def valence (q z:Badge G)(y:Full.Grid n 3)(j:P)(h:ℝ):ℂ:=↑(CardC q true h (y 0) (Stele z false (y j) h) (Stele z false (y j) h))
lemma out_charge (d:Diorama T u p)(j:P)(hj:j≠0)(a b:Badge G): Tendsto (fun i=> valence a b (u i) j (T.gap i)) atTop (𝓝 0):=by
 let v:= fun (j:P)(i:ℕ)=>u i j
 have hv:=looked d 0 j; have hz:=sub_ne_zero.mpr (d.ht.ne hj); have H:= hop_read T a b b true false false (v 0) (v j) (v j) hz hz hv hv; rw [show colorF b.2 b.2 a.2=0 from by unfold colorF;rw [ad_diag0,inner_zero_left],zero_mul] at H
 simpa only [ofReal_zero] using! continuous_ofReal.continuousAt.tendsto.comp H
lemma plates (a b:Badge G)(o:Full.Grid n 3)(j:P)(t:ℝ) : valence a b o j t= 2*∑ i: Who G 6,∑ k:Who G 6,∑ l:Who G 6, ct a true i *ct b false k *ct b false l *(echoLeg t (o 0) i.val (arise t o (j,k)) (arise t o (j,l)):ℂ) := by
 let F(i:Who G 6): FullT G n →ₗ[ℝ] FullT G n→ₗ[ℝ] ℝ:= echoLeg t (o 0) i.val; let X(i:Who G 6):=arise t o (j,i)
 have hh {I E:Type}[Fintype I][AddCommGroup E][Module ℝ E](F:I→ E→ₗ[ℝ] E→ₗ[ℝ] ℝ)(U:I→ E)(p q:I→ℝ): (↑(2 * ∑ i:I,p i*F i (∑ i,q i • U i) (∑ i,q i • U i):ℝ):ℂ)=2 *(∑ i:I,∑ j:I,∑ k:I,(p i:ℂ)*(q j:ℂ)*(q k:ℂ)*(F i (U j) (U k):ℂ)):=by
    simp only [map_sum,map_smul,LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul, Finset.mul_sum, ofReal_sum,ofReal_ofNat,ofReal_mul]
    apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>by ring
 unfold valence Stele CardC; convert hh F X (token a true) (token b false) using 1; simp only [F,X,arise]
-- DO grouped evaluation, use 2* both sides (C normalized)
def dressed (j:P)(x y:Trio G): Players G 3 6:= if j=1 then ![x,y,seaU G] else ![x,seaU G,y]
lemma distress (j:P)(o:Full.Grid n 3)(t:ℝ): ∃ L: Trio G→ₗ[ℂ] Trio G →ₗ[ℂ] ℂ,∀ a b,L a b=ZeroR o t (dressed j a b):= by
 obtain ⟨L,H⟩:= tall_eq (G:=G) o t; obtain ⟨M,h⟩:= stamps L
 unfold dressed; by_cases e:j=1
 · simp_rw [if_pos e]; exact ⟨(LinearMap.llcomp ℂ (Trio G) (Trio G →ₗ[ℂ] ℂ) ℂ (LinearMap.applyₗ (seaU G)) ∘ₗ M), fun a b=> (h a b _).trans (H _)⟩ -- names
 simp_rw [if_neg e]; refine ⟨(LinearMap.applyₗ (R:=ℂ) (seaU G) ∘ₗ M), fun a b=>?_⟩; exact (h _ _ _).trans (H _)
lemma starlap (j:P)(he:j≠0)(a b c:Who G 6): dict (j,c) (dict (j,b) (dict (0,a) (SlateZ G)))= dressed j (D1 a (orbZ G)) (D1 c (D1 b (seaU G))) := by
 rcases tick_any he with rfl|rfl
 · rw [at0 _,at1 _,at1]; rfl
 rw [at0 _,at2 _,at2];rfl
lemma tac2 (j:P)(hj:j≠0)(o:Full.Grid n 3)(s:ℝ) : 2*tracC o s 0 j (SlateZ G)= ∑ a:Badge G,∑ b:Badge G,∑ c:Badge G,∑ k:Badge G, (3*tau a b c*valence a k o j s * ZeroR o s (dressed j (β b * β c) 1)) := by
 obtain ⟨L,h⟩:= distress (G:=G) j o s
 let X(i k l:Who G 6):ℂ:=↑(echoLeg s (o 0) i.val (arise s o (j,k)) (arise s o (j,l)))
 let f (w x y:Who G 6)(a b c k:Badge G) :ℂ:= 3*tau a b c * ct a true w * ct k false x* ct k false y * X w x y * L (β b*β c) 1
 have hx(w x y:Who G 6): changeD o s (SlateZ G) (0,w) (j,x) (j,y) = ∑ a:Badge G,∑ b:Badge G,∑ c:Badge G,∑ k:Badge G,f w x y a b c k:=by
    unfold changeD; rw [starlap j hj,← h]; conv_lhs => arg 1; dsimp only; change X w x y
    rw [orb_one,sea_twice]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
    -- outer order inspect
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _=> Finset.sum_congr rfl fun k _=> by unfold f β; ring
 unfold tracC; simp_rw [hx,S34 f, Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl;intro k _; rw [plates, ← h]; change _= 3*tau a b c*(2*∑ i:Who G 6,∑ l:Who G 6,∑ v:Who G 6, ct a true i*ct k false l*ct k false v*X i l v)*_
 simp only [Finset.mul_sum,Finset.sum_mul]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun l _=>Finset.sum_congr rfl fun v _=>by unfold f; ring
end YM.RG11.FirstW.Branch
