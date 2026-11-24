import YM.MS.Motif.Beat
import YM.MS.Motif.Matrix

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Native
open scoped Topology ContDiff InnerProductSpace
variable {A:Type} {G:Gauge} {n:ℕ} {b c:Bool}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 " ⋄ "=> product S
variable {F X:Rack G n} {U H W: Mield G n}
lemma section_p (h:fieldSection false F)(hp:fieldSection false X) : fieldSection false (F ⋄ X):= by intro k i; rw [D_product,h k i,hp k i]; simp
lemma section_m (h:fieldSection false F)(k:SectorP n→+ℂ): fieldSection false (moment k F):= by intro i v; rw [moment_D,h i v]; simp
lemma section_n (i:Chan G n)(t:SectorP n→ℂ): fieldSection false (note (onX false i) t):=by intro j v; rw [nodeD]; simp [onX]; ext l; cases l <;> rfl
lemma section_sum (s:Finset A){u:A→ Rack G n}(h:∀ i∈s,fieldSection false (u i)): fieldSection false (∑ i∈ s,u i):= by intro i v; rw [map_sum]; exact Finset.sum_eq_zero fun i hi=> h i hi .. -- placeholder applied full equality
structure Mood (b:Bool)(F:Mield G n): Prop where
    tune : un F b
    rank i: fieldSection false (F i)
lemma Mood.add (h:Mood b U)(hp:Mood b H): Mood b (U+H):= ⟨fun i=> (h.tune i).add (hp.tune i),fun i v t=> by simp only [Pi.add_apply,map_add,add_zero,h.rank i v t,hp.rank i v t] ⟩ -- bool simp
lemma Mood.smul (h:Mood b U)(q:ℂ): Mood b (q • U):= ⟨ fun i=> (h.tune i).smul q,fun i v t=> by simp only [Pi.smul_apply,map_smul,smul_zero,h.rank i v t]⟩
lemma Mood.neg (h:Mood b U): Mood b (-U):= by simpa only [neg_one_smul] using h.smul (-1)
lemma Mood.sub (h:Mood b U)(he:Mood b H): Mood b (U-H):= by rw [sub_eq_add_neg]; exact h.add he.neg
lemma Mood.jawn (h:Mood b U)(ht:Mood c H): Mood (b ^^ c) (jaw G n U H):= by
   refine ⟨jaw_p h.tune ht.tune,fun i=>?_⟩; rw [chew]; refine section_sum _ (fun i _=> section_sum _ (fun j _=>?_)); intro v t; rw [map_smul, section_p (h.rank i) (ht.rank j)]; simp
def forge (s:Op (Shore G n) ℂ) : Mield G n →ₗ[ℂ] Mield G n where
    toFun F i:=s (F i)
    map_add' F H:=funext fun i=> map_add _ (F i) ( H i)
    map_smul' c F:= funext fun i=> map_smul _ c (F i)
lemma lock (s:Op (Shore G n) ℂ)(F:Mield G n)(i:G.ColorIndex): forge s F i=s (F i):= rfl
lemma Mood.moment (u:SectorP n→+ℂ)(h:Mood b U): Mood b (forge ( Motif.moment u) U) where
    tune i l hl:= by rw [lock,moon, h.tune i l hl, mul_zero]
    rank i:= section_m (h.rank i) _
lemma exchange (s:SectorP n→+ℂ): forge (moment s) (jaw G n U W) = jaw G n (forge (moment s) U) W + jaw G n U (forge (moment s) W):= by
    ext1 i; simp only [lock,chew,map_sum,map_smul,blends,smul_add,Pi.add_apply,Finset.sum_add_distrib]
lemma derive (h:un U b) {V:Chan G n→Rack G n}(he:Lamp V): forge (dot V) (jaw G n U H)=jaw G n (forge (dot V) U) H +(cross true b:ℂ) • jaw G n U (forge (dot V) H):= by
    funext i; simp_rw [Pi.add_apply,Pi.smul_apply,lock, chew, map_sum,map_smul,dot_pair he (h _),smul_add, Finset.sum_add_distrib]; simp_rw [Finset.smul_sum, smul_comm (cross true b:ℂ)] ; rfl -- lock order simp
end YM.MS.Motif
