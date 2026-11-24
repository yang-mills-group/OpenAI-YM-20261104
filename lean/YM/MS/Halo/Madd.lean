import YM.MS.Garment.Apatite
import YM.MS.Halo.Air
import YM.MS.Motif.K2
import YM.MS.Wilson.DyedAction

set_option autoImplicit false
noncomputable section
namespace YM.MS.Halo
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Pilot Garment Color Book
open Motif Native
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ} {b:Bool} {z:ℂ} {F H:Rack G n} {U Y:Mield G n}
local notation "S"=> field (Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product S
lemma glob_prod (ξ:G.El)(F H:Rack G n): repeatC ξ (F ⋄ H)= repeatC ξ F ⋄ repeatC ξ H:= by rw [ ← brush,circle_prod]
lemma glob_m (ξ:G.El)(a:Arts.L n) : repeatC ξ (rowP a F)=rowP a (repeatC ξ F):= by funext w; rw [ ← brush,rowP,beamMoon,moon]; rfl
abbrev Apple (U:Mield G n): Prop:= ∀ ξ:G.El,∀ k:G.ColorIndex, repeatC ξ (U k)= ∑ j:G.ColorIndex,wc ξ j k • U j
namespace Apple
lemma add (hx:Apple U)(he:Apple Y): Apple (U+Y):= by intro i j; simp_rw [Pi.add_apply,map_add,smul_add,hx i, he i,Finset.sum_add_distrib]
lemma sub (hx:Apple U)(he:Apple Y): Apple (U-Y):= by intro i j; simp_rw [Pi.sub_apply,map_sub,smul_sub,hx i,he i, Finset.sum_sub_distrib]
lemma smul (hx:Apple U)(c:ℂ): Apple (c • U):= by intro i j; simp_rw [Pi.smul_apply,map_smul,hx i,Finset.smul_sum, smul_comm c _]
lemma pureC (b:Bool)(a: Option (Arts.L n)): Apple ( lip b a: Mield G n ):= by
    intro k j; funext w; rw [← brush,lip,usesLeaf]; rcases w with _|⟨⟨⟨i,s⟩,p⟩,_|u⟩ <;> simp [Finset.sum_apply,lip,Motif.leaf,note,mono,Garment.dye,onX]; by_cases hx:i=(a,b) <;> simp [hx] -- patch local
lemma leaf (a:Arts.L n): Apple (Motif.A n G a):= pureC false _
lemma runs (hv:Apple U)(a:Arts.L n): Apple (axisP a U):= by intro k i; simp_rw [axisP,lock, glob_m, hv _,map_sum,map_smul]
private lemma stage0 (F:G.ColorIndex→G.ColorIndex→G.ColorIndex→ G.ColorIndex→Rack G n): ∑ i,∑ j,∑ k,∑ p,F i j k p=∑ k,∑ p,∑ i,∑ j,F i j k p:= by let H(i j:G.ColorIndex × G.ColorIndex):= F i.1 i.2 j.1 j.2; obtain he: ∑ i:G.ColorIndex × G.ColorIndex,∑ j:G.ColorIndex×G.ColorIndex,H i j= ∑ j:G.ColorIndex × G.ColorIndex,∑ i:G.ColorIndex×G.ColorIndex,H i j:= Finset.sum_comm; simpa only [ Fintype.sum_prod_type] using he
lemma r_eq (hx: Apple U)(hv: Apple Y) : Apple (jaw G n U Y) := by
    intro z i; simp only [ chew, map_sum,map_smul,glob_prod,hx z,hv z, LinearMap.sum_apply,LinearMap.smul_apply,Finset.smul_sum]; rw [stage0]; conv_rhs=>rw [Finset.sum_comm]; -- order collapse
    rw [ Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; conv_rhs => rw [Finset.sum_comm];
    apply Finset.sum_congr rfl; intro b _; simp_rw [smul_smul, ← Finset.sum_smul]; congr 1
    have ht(j k:G.ColorIndex): rune j k i*(wc z b k *wc z a j)= ↑(weight z a j*weight z b k*letterLie j k i):= by push_cast [wc,rune]; ring
    have Hv(j:G.ColorIndex): wc z j i*rune a b j= ↑(letterLie a b j*weight z j i):= by push_cast [wc,rune]; ring
    simp_rw [ht,Hv, ← Complex.ofReal_sum, Paint.tensorT ]
variable (a i:Arts.L n)
lemma heat (h:Apple U): Apple (convoke z a U):= by rw [convoke, LinearMap.add_apply,LinearMap.smul_apply]; exact (h.runs a).add (((leaf a).r_eq h).smul _)
lemma spicy : Apple (cur z a i:Mield G n):= Apple.add (Apple.sub ((leaf i).runs a) ( (leaf a ).runs i)) ( Apple.smul (( leaf a ).r_eq ( leaf i )) _)
end Apple
end YM.MS.Halo
