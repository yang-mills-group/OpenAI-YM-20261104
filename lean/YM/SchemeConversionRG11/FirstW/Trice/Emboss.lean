import YM.SchemeConversionRG11.FirstW.Trice.Pale
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{F:Labels.Frames G}{u:∀ i,Full.Grid (T.period i) 3}{p:Nodes} {W:Wash}{R:ℝ}{n:Side}
def SlateZ (G:Gauge): Players G 3 6:= ![orbZ G, seaU G,seaU G]
lemma basic_eq (F:Labels.Frames G): (cloak F ∘ basic F)=SlateZ G := by funext i; fin_cases i; exact orbC F; exact seaC F _ (by decide); exact seaC F _ (by decide)
lemma at0 (p:Players G 3 6)(a: Who G 6): dict (0,a) p= ![D1 a (p 0),p 1,p 2]:= by unfold dict; funext i; fin_cases i<;>rfl
lemma at1 (p:Players G 3 6)(a: Who G 6): dict (1,a) p= ![p 0,D1 a (p 1),p 2]:= by unfold dict; funext i; fin_cases i<;>rfl
lemma at2 (p:Players G 3 6)(a: Who G 6): dict (2,a) p= ![p 0,p 1,D1 a (p 2)]:= by unfold dict; funext i; fin_cases i<;>rfl
lemma chopped (a b:Who G 6)(hp:p∈conf 3): Rule p 1 (D1 a (D1 b (seaU G))) (seaU G)=0 ∧ Rule p 1 (seaU G) (D1 a (D1 b (seaU G)))=0:= by
 obtain ⟨L,H⟩:=stamped_rule (G:=G) p; simp only [← H,sea_twice,map_sum, map_smul, LinearMap.sum_apply,LinearMap.smul_apply]; simp only [H,(tax_nil p hp).1,(tax_nil p hp).2,smul_zero, Finset.sum_const_zero,and_self]
lemma tax_shores (hp:p∈conf 3)(a b:At G 3 6)(hh:a∈apart G 6 0)(ht:b∈apart G 6 0): amount p (dict b (dict a (air (SlateZ G) 0)))=0 := by
 obtain ⟨i,a⟩:=a; obtain ⟨j,b⟩:=b; let X:= air (SlateZ G) 0; have h(i:Fin 3)(he:i≠0): i=1∨i=2:= (full_order 0 i).resolve_left he; -- defeq
 rcases h i (Finset.mem_filter.mp hh).2 with rfl|rfl <;> rcases h j (Finset.mem_filter.mp ht).2 with rfl|rfl
 · rw [at1 X,at1]; exact (chopped b a hp).1
 · rw [at1,at2]; exact (tax_nilS p hp a b).1
 · rw [at2,at1]; exact (tax_nilS p hp b a).1
 rw [at2 X,at2]; exact (chopped b a hp).2
lemma dead_cost (L:Pack F)(u:P)(h:u≠0): L.val (basic F u)=0:=(suitsP L).sunk _ (sink_zero _ (show 4<6 by decide) (Triangle.lower_basic _ u h))
lemma foil_cost (p:P)(hp:p≠0)(Z:ℕ→Pack F)(s:ℕ)(W:Wash)(T:Itinerary)(X Y:Field4 G): bleach T W (Z s) s (basic F p) X Y=0:= by
 rw [smear,dead_cost (Z s) p hp,map_zero]; simp only [map_zero, sub_zero,dew_val,saleF,burn_eq]; have h(i j k:Who G 6) := tangI F i j k (basic F p) 4 (by decide) (Triangle.lower_basic _ p hp);simp_rw [h,zero_mul, Finset.sum_const_zero]; simp
lemma tend_t {I:Type}(s:Finset I)(f:I→ℕ→ℂ)(h:∀ i∈s,Tendsto (f i) atTop (𝓝 0)): Tendsto (fun k=>∑ i∈s,f i k) atTop (𝓝 0):= by simpa only [Finset.sum_const_zero] using (tendsto_finsetSum _ h)
lemma burn_tax (p:Nodes) (d:Diorama T u p)(v:P) (hz:W.rOut<R)(ht:∀ i j:P,i≠ j → 8*R<‖p i-p j‖)(hc:MarkGrid T c)(Z:ℕ→Pack F)(H:stampB F Z T W) : Tendsto (billedC F W T u Z (basic F v) (SlateZ G) v) atTop (𝓝 0) := by
 unfold billedC; by_cases hv:v=0
 · subst v; apply tend_t
   intro i hi; -- rename collide hp
   have hh(j:At G 3 6)(he:j∈apart G 6 0): Coal T W R (fun s=>radX 0 (u s) (T.gap s) 6 j):= prints d 0 j hz (ht _ 0 (Finset.mem_filter.mp he).2)
   refine tend_t _ _ ?_; -- replace
   intro j hj; obtain ⟨b,h⟩:= burn_paid (fun s=>radX 0 (u s) (T.gap s) 6 i) (fun s=>radX 0 (u s) (T.gap s) 6 j) hz (hh i hi) (hh j hj) (basic F 0) H hc; simpa only [tax_shores d.ht _ _ hi hj,mul_zero] using! h.mul (fortune d (dict j (dict i (air (SlateZ G) 0))))
 simp_rw [foil_cost v hv,smul_zero,zero_mul,Finset.sum_const_zero]; exact tendsto_const_nhds
end YM.RG11.FirstW.Branch
