import YM.MS.Arts.Range
import YM.MS.Wilson.LieWords

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Flux Landau Arts Native
open scoped Topology ContDiff InnerProductSpace
variable {A:Type} {G:Gauge} {n:ℕ} {H:Rack G n} {b c:Bool}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:67 " ⋄ "=> product S
abbrev Mield (G:Gauge)(n:ℕ):= G.ColorIndex→ Rack G n
abbrev un (F:Mield G n)(b:Bool): Prop :=∀ i,Pure S b (F i) -- abbrev hygienic? n binder implicit
variable {U F W:Mield G n}
def rune (i j k:G.ColorIndex): ℂ:=letterLie i j k
theorem r_ortho (i j k:G.ColorIndex): rune i j k = -rune j i k:= by unfold rune; rw [scaled_tensor,scaled_tensor,Only.ad_anti,inner_neg_left]; push_cast; rfl
theorem r_rule (i j k l:G.ColorIndex) : ∑ u:G.ColorIndex,rune j k u*rune i u l =(∑ u:G.ColorIndex,rune i j u*rune u k l)+∑ u:G.ColorIndex,rune i k u*rune j u l:= by
   let f(i j k l:G.ColorIndex) := ∑ u:G.ColorIndex,rune i j u*rune u k l; have ht (i j k l:G.ColorIndex): (∑ u:G.ColorIndex,rune i j u*rune k u l)= -f i j k l:= by simp_rw [r_ortho k _ l, mul_neg,Finset.sum_neg_distrib]; rfl
   rw [ht,ht]; unfold f; suffices he:(∑ u:G.ColorIndex, (rune i j u*rune u k l +rune j k u*rune u i l+rune k i u*rune u j l))=0 by simp_rw [r_ortho k i,neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib] at he; linear_combination (norm:=abel) -he
   have H(i j k l:G.ColorIndex) := Bare.Focus.Metric.acts (cartan G Unit) ((),i) ((),j) ((),k) ((),l); specialize H i j k l; simp only [ Fintype.sum_prod_type, Fintype.sum_unique,story] at H; unfold rune; exact_mod_cast H
abbrev bite (n:ℕ)(G:Gauge):= product (R:=ℂ) (field (P:= SectorP n) (Landau.parity (C:=G.ColorIndex) (A:=Arts.L n)))
def mow (F U:Mield G n): Mield G n:= fun i=> ∑ j:G.ColorIndex,∑ k:G.ColorIndex, rune j k i • (F j ⋄ U k)
def jaw (G:Gauge)(n:ℕ):Mield G n→ₗ[ℂ] Mield G n→ₗ[ℂ] Mield G n:= LinearMap.mk₂ ℂ mow (fun f g h=> funext fun i=> by simp [mow,smul_add,Finset.sum_add_distrib]) (fun s f h=> funext fun i=> by simp only [mow,Pi.smul_apply,map_smul,LinearMap.smul_apply, Finset.smul_sum]; simp_rw [smul_comm s _]) (fun f g h=> funext fun i=> by simp [mow,smul_add, Finset.sum_add_distrib]) (fun s f g=> funext fun i=> by simp only [mow, Pi.smul_apply,map_smul, Finset.smul_sum]; simp_rw [smul_comm s _] )
lemma chew (i:G.ColorIndex)(F U:Mield G n): jaw G n F U i=∑ j:G.ColorIndex,∑ k:G.ColorIndex, rune j k i • ( F j ⋄ U k ):=rfl
lemma jaw_p (h:un F b)(ht:un U c): un (jaw G n F U) (b ^^ c):= fun i=> by rw [chew]; exact Pure.sum _ (fun j _=> Pure.sum _ (fun k _=> ((h j).prod (ht k)).smul _))
lemma jaw_skew (h:un F b)(hv:un U c): jaw G n F U= (- (cross b c:ℂ)) • jaw G n U F := by
   ext1 i; rw [Pi.smul_apply,chew,chew,Finset.sum_comm]; simp_rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_
   rw [r_ortho k j,(h _).times_comm (hv _), neg_smul,neg_smul]; cases b <;> cases c <;> simp
lemma law (hf:un F b)(he:un U c): jaw G n F (jaw G n U W)=jaw G n (jaw G n F U) W+ (cross b c:ℂ) • jaw G n U (jaw G n F W):= by
    funext l; -- ℂ-Lie, sum coordinates reorder. internal helper
    let X (i j k:G.ColorIndex) := (F i⋄ U j) ⋄ W k
    let v(i j k r:G.ColorIndex): ℂ:= rune i j r*rune r k l; let y (i j k r:G.ColorIndex):ℂ:=rune i j r*rune k r l
    have h0 (a b c:Mield G n)(l:G.ColorIndex): jaw G n a (jaw G n b c) l=∑ i:G.ColorIndex,∑ j:G.ColorIndex,∑ k:G.ColorIndex, (∑ r:G.ColorIndex, rune j k r*rune i r l) • ((a i⋄ b j) ⋄ c k):= by
       simp only [chew,map_sum,map_smul,Finset.smul_sum, ← times_assoc,smul_smul,Finset.sum_smul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]; simp only [mul_comm]
    have h1 (a b c:Mield G n): jaw G n (jaw G n a b) c l=∑ i:G.ColorIndex,∑ j:G.ColorIndex,∑ k:G.ColorIndex,(∑ t:G.ColorIndex,rune i j t*rune t k l) • (( a i ⋄ b j) ⋄ c k):= by
       have front (f:G.ColorIndex→ G.ColorIndex→ G.ColorIndex→ Rack G n): ∑ r:G.ColorIndex,∑ i:G.ColorIndex,∑ j:G.ColorIndex,f r i j=∑ i:G.ColorIndex,∑ j:G.ColorIndex,∑ r:G.ColorIndex,f r i j:= by rw [ Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [ Finset.sum_comm]
       simp only [chew,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Finset.smul_sum,smul_smul,sum_smul]
       -- r k i j swap to k i j r then swap block push k to third.
       rw [ Finset.sum_comm]; let F(r k i j:G.ColorIndex):= (rune r k l*rune i j r) • (( a i ⋄ b j ) ⋄ c k)
       change ∑ k:G.ColorIndex,∑ r:G.ColorIndex,∑ i:G.ColorIndex,∑ j:G.ColorIndex,F r k i j=_; simp_rw [front (fun r i j=>F r _ i j)]; rw [front]; -- may loop
       unfold F; simp only [mul_comm]
    rw [Pi.add_apply,Pi.smul_apply,h0,h1,h0]; simp_rw [Finset.smul_sum]; -- swap sum for right second term use rw [...]
    conv_rhs => arg 2; rw [ Finset.sum_comm];
    simp only [ ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_ ; rw [r_rule, (he j).times_comm ( hf i ), map_smul, LinearMap.smul_apply, smul_comm (∑ x:G.ColorIndex, rune i k x*rune j x l), smul_smul (cross b c:ℂ), cross_comm c b, cross_cross, one_smul,add_smul ]
end YM.MS.Motif
