import YM.SchemeConversionRG11.FirstW.Trice.Grime
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{G:Gauge}{p:Nodes}{n:Side}{r:ℕ}
lemma erased_1 (p:Nodes) (hp:p∈conf 3)(a b c:Who G 6): Rule p (D1 b (D1 c (orbZ G))) (D1 a (seaU G)) (seaU G) = 0 ∧ Rule p (D1 b (D1 c (orbZ G))) (seaU G) (D1 a (seaU G)) = 0:= by
 obtain ⟨L,H⟩:= stamped_rule (G:=G) p; simp only [←H,orb_twice,sea_one]; simp only [seaU, map_add,map_smul,map_sum,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.smul_apply]
 simp only [H]; simp only [show ∀ a b c d:Badge G, Rule p (Glyph a true) (Glyph b false) (Glyph c false*Glyph d false)=0 from fun a b c d=> (spend_pair hp a b c d).1, show ∀ a b c d:Badge G,Rule p (Glyph a true) (Glyph c false*Glyph d false) (Glyph b false)=0 from fun a b c d=> (spend_pair hp a b c d).2,smul_zero,Finset.sum_const_zero,and_self,add_zero]
lemma erased_2 (p:Nodes) (hp:p∈conf 3)(a b c:Who G 6): Rule p (orbZ G) (D1 a (seaU G)) (D1 b (D1 c (seaU G))) = 0 ∧ Rule p (orbZ G) (D1 b (D1 c (seaU G))) (D1 a (seaU G)) = 0:= by
 obtain ⟨L,H⟩:= stamped_rule (G:=G) p; simp only [←H,orbZ,sea_twice];simp only [sea_one, map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply]
 simp only [H]; simp only [show ∀ a b c d:Badge G, Rule p (Glyph a true*Glyph b true*Glyph c true) (Glyph d false) 1=0 from fun a b c d=> (three_same hp a b c d).1, show ∀ a b c d:Badge G,Rule p (Glyph a true*Glyph b true*Glyph c true) 1 (Glyph d false)=0 from fun a b c d=> (three_same hp a b c d).2,smul_zero,Finset.sum_const_zero,and_self]
lemma tax_nil (p:Nodes) (hp:p∈conf 3): Rule p 1 1 (seaU G) = 0 ∧ Rule p 1 (seaU G) 1 = 0:= by
 obtain ⟨L,H⟩:= stamped_rule (G:=G) p; simp only [←H,seaU, map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply]
 simp only [H]; simp only [show ∀ a b:Badge G, Rule p 1 1 (Glyph a false*Glyph b false)=0 from fun a b=> (one_u hp a b).1, show ∀ a b:Badge G,Rule p 1 (Glyph a false* Glyph b false) 1=0 from fun a b=> (one_u hp a b).2.1,smul_zero,Finset.sum_const_zero,and_self]
lemma tax_nilS (p:Nodes) (hp:p∈conf 3)(a b:Who G 6): Rule p 1 (D1 a (seaU G)) (D1 b (seaU G)) = 0 ∧ Rule p 1 (D1 b (seaU G)) (D1 a (seaU G)) = 0:= by
 obtain ⟨L,H⟩:= stamped_rule (G:=G) p; simp only [←H,sea_one, map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply]
 simp only [H]; simp only [show ∀ a b:Badge G, Rule p 1 (Glyph a false) (Glyph b false)=0 from fun a b=> (one_u hp a b).2.2,smul_zero,Finset.sum_const_zero,and_self]
end YM.RG11.FirstW.Branch
