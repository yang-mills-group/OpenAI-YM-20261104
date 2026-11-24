import YM.FormalBulk08.Vale.Paddle
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
lemma rawSeen (P:Pot G)(a:hue G)(h:Ritual P i) j k r (hp:i≤j): Light (P k r) (fun n:Side=>rancho (Kemp.banner j P n) k r):= by
   obtain ⟨s,C,hs,H⟩:= h.health (0,Exterior.coord 0,a) _ r; simp_rw [badge _ h.young h.committees hp]; exact (sieve_kalm _ H hs.le).1
lemma sentience (a:hue G){T S:Pot G}(h:Ritual T t)(hp:Ritual S t)(he:∀ p:Side,Kemp.banner t T p=Kemp.banner t S p): T=S:= by
   funext i j x; refine tendsto_nhds_unique (rawSeen T a h _ i j le_rfl x) ((rawSeen S a hp _ i j le_rfl x).congr' (.of_forall fun n=>?_)); dsimp only;rw [he]
lemma remitted (a:hue G)(T S:Pence)(e:T*S=1)(L:List I)(p:I→Pot G)(l:I→ℕ)(h:∀ i∈L,Ritual (p i) (l i)): stamp T S (packV p L)=packV (fun i=>stamp T S (p i)) L:= by
   have hp:=orchestra p l L h a; have ht i hi:= stab a (h i hi) e; apply sentience a (stab a hp e) (orchestra _ l L ht a); intro U
   rw [(boarding a _ hp.health hp.young hp.committees T S).2.2.2 U,summons _ _ _ h a,summons _ _ _ ht a, show canter T S _ (L.map _).prod=_ from novel_map_prod (fun i=>Kemp.banner (l i) (p i) U) (canter T S _).toMonoidHom L]
   apply congr_arg List.prod; refine List.map_congr_left ?_; intro i hi; exact ((boarding a (p i) (h i hi).health (h i hi).young (h i hi).committees T S).2.2.2 U).symm
lemma road_sub {X:Type} (T S:Pence)(p q:OrbitV X): stamp T S (p-q)=stamp T S p-stamp T S q:= by funext i j; simp [stamp,Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]
lemma road_add {X:Type} (T S:Pence)(p q:OrbitV X): stamp T S (p+q)=stamp T S p+stamp T S q:= by funext i j; simp [stamp,Pi.add_apply,smul_add,Finset.sum_add_distrib]

variable {K:KernelChoices}(P:Flight j t)(R:Lodge P.patch)(ρ:ChartRatio G)(W:Pot G)(h:P.patch.Branches K G)
variable (a:hue G)(V:I→Pot G)(μ:I→ℕ)(L:List I)(hv:∀ i∈L,Ritual (V i) (μ i))(hP:Story W (pink K.penalty P.wing))(hs:LocalRatio ρ)(ht:4 ≤ t)

/-- One mark operation, not normalized products of coincidences. -/
def fallout := enterStep P R W a ρ h (L.map μ).sum (packV V L)-packV (fun i=> enterStep P R W a ρ h (μ i) (V i)) L
include hv hP hs ht
lemma glacier (o:edgeL G): let z:=epoch a P R K W ρ h
                fallout P R ρ W h a V μ L=stamp (bookH z) (bookU z) (fun e r=>∑ i∈Finset.range ((L.map μ).sum+3*e+1),jetty (coastRight _ _ _) (morsel P R ρ W h V L i e r)):= by
   intro z; let Y (i):= braise P R W (V i) ρ h (μ i); let X:=braise P R W (packV V L) ρ h (L.map μ).sum
   have hp(k)(hk): Ritual (Y k) (μ k):= paragon o P R W ρ h hP hs ht (hv k hk) (fun n=>Classical.choice (chooseable n _ _))
   change stamp _ _ X-packV (fun i=>stamp (bookH z) (bookU z) (Y i)) L=_; rw [← remitted a _ _ (book_equal z) L Y μ hp,← road_sub]; apply congr_arg; funext i j; exact matter_out P R ρ W h a V μ L hv hP hs ht i j
end YM.FormalBulk08.Vale
