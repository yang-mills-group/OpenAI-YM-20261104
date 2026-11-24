import YM.MS.Motif.Pulp

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Native
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ} {U V:Mield G n} {b:Bool}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
variable (z:ℂ)
local notation "g"=> cwave n G
local notation "Ω" => jaw G n
local notation "σ"=> dot (applyS z G n)
local notation "Sg"=> forge σ
local notation "Γ"=> A n G
lemma civil_d (p:Arts.L n)(h:un U b): convoke z p (Ω U V)= Ω (convoke z p U) V+ Ω U (convoke z p V):= by
   simp only [convoke, LinearMap.add_apply,LinearMap.smul_apply, map_add,map_smul, exchange, law (realA (G:=G) p).tune h, cross_false, one_smul,smul_add]; abel
lemma twist (a c: Arts.L n): convoke z a (convoke z c U)-convoke z c (convoke z a U)= z • Ω (cur z a c) U:= by
   have he(a c:Arts.L n): axisP a (axisP c U)=axisP c (axisP a U):= funext fun k=> rail (δ a) (δ c)
   have ht: Ω (Γ a) (Ω (Γ c) U)= Ω (Ω (Γ a) (Γ c)) U+ Ω (Γ c) (Ω (Γ a) U):= by simpa only [cross_false,one_smul] using law ( realA (G:=G) a ).tune ( W:=U) (realA c).tune
   simp only [convoke,LinearMap.add_apply,cur,F₀,map_add,map_sub,LinearMap.sub_apply,map_smul,LinearMap.smul_apply,exchange, he a c,ht,smul_add,smul_sub]; abel
lemma horr (a c: Arts.L n): Sg (cur z a c)=z • Ω (cur z a c) g:= by
   rw [← twist]; conv_lhs=> rw [cur,F₀,map_add,map_smul,map_sub,deriv_v z (realA a), S_action,S_action, cross_false',one_smul];
   simp only [ comm_d,S_action]; -- ∂ first
   rw [show Ω (convoke z a g) (Γ c)= -Ω (Γ c) (convoke z a g) from ?_];
   ·
     simp only [convoke,LinearMap.add_apply,LinearMap.smul_apply,smul_add,smul_neg]; abel -- may need map_add to normalize both
   simpa only [cross_false',neg_one_smul] using jaw_skew ( heatSA z true g ghMd a ).tune (realA c).tune
end YM.MS.Motif
