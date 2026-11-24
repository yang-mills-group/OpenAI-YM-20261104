import YM.OPE.Compatible.Dale.Chest
import YM.PertExtension.OrbHaar
/-!
# exact local chart change preserving product Haar
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory
open scoped Topology BigOperators ComplexConjugate Classical
abbrev Gem (G:Gauge)(α:Type)[Fintype α] :=Measure.pi fun _ : α=> G.probHaar
section
variable {D V:Type}{G:Gauge}{K:Type}[Group K][TopologicalSpace K][IsTopologicalGroup K]
variable {R: Score D V}{B:Set V} (T:R.Stand B)
namespace Score.Stand
instance [Fintype D]: Fintype T.Free:=by dsimp only [Free]; infer_instance
instance [Fintype D]: Fintype T.Stable:=by dsimp only [Stable]; infer_instance
@[fun_prop] lemma sweepC : Continuous (T.sweep (K:=K)):=by
    apply continuous_pi; intro i; induction z:T.flick i using Nat.strong_induction_on generalizing i with
    | h r ho=>
       by_cases ht:i∈ Bᶜ
       · let j : ↥(Bᶜ) :=⟨i,ht⟩; let q:=T.point j
         simp_rw [show i=j.val from rfl,T.sweptJ]; unfold taste; split <;>
           exact (ho _ ((T.bump j).trans_eq z) _ rfl).mul (by fun_prop)
       simp_rw [T.swept _ (not_not.mp ht)]; exact continuous_const
@[fun_prop] lemma dellC : Continuous (T.dell (K:=K)):=by apply continuous_pi; intro i; unfold dell dress; fun_prop
omit [Group K] [IsTopologicalGroup K] in
@[fun_prop] lemma citeC : Continuous (fun u:(T.Stable→K) × (T.Free→K)=> T.cite u.1 u.2):=by apply continuous_pi;intro i; unfold cite;split<;>fun_prop
@[fun_prop] lemma delegates (H:R.Stand B): Continuous ((T.drapeX (K:=K) H):_→_):= H.dellC.comp (show Continuous _ from T.citeC.comp (continuous_const.prodMk (show Continuous (fun i:T.Free→K=>i) from continuous_id')))
variable [Fintype D]
lemma citeHaar : MeasurePreserving (fun u:(T.Stable→G.El) × (T.Free→ G.El)=> T.cite u.1 u.2) ((Gem G T.Stable).prod (Gem G T.Free)) (Gem G D):=by
   let f := fun u:(T.Stable→G.El) × (T.Free→ G.El)=> T.cite u.1 u.2
   have hf:Measurable f := T.citeC.measurable
   refine ⟨hf,Eq.symm ?_⟩; apply Measure.pi_eq; intro t ht
   rw [Measure.map_apply hf (MeasurableSet.univ_pi ht)]
   have he: f ⁻¹' (Set.pi univ t)=(Set.pi univ (fun i:T.Stable=>t i)) ×ˢ ((Set.pi univ (fun i:T.Free=>t i))) := by
      ext ⟨x,y⟩; simp only [mem_prod,Set.mem_pi,mem_preimage,mem_univ,true_implies]
      refine ⟨fun h=>⟨fun i=>by rw [← T.keptZ x y i]; exact h _, fun i=> by rw [← T.kept x y i]; exact h _⟩,?_⟩
      rintro ⟨h,H⟩ i
      unfold f cite; split_ifs
      next hv=> exact h ⟨_,hv⟩
      next hv=> exact H ⟨_,hv⟩
   rw [he,Measure.prod_prod,Measure.pi_pi,Measure.pi_pi]; convert! Fintype.prod_subtype_mul_prod_subtype T.Branch (fun i=>G.probHaar (t i))
omit [TopologicalSpace K] [IsTopologicalGroup K] [Fintype D] in
lemma sweepZ (u v:D→K)(h:∀ p:T.Stable,u p=v p): T.sweep u=T.sweep v:=by
    funext i; induction z:T.flick i using Nat.strong_induction_on generalizing i with
    | h r ho=>
       by_cases H:i∈ Bᶜ
       · let p : ↥(Bᶜ):=⟨i,H⟩; change T.sweep u p.val=T.sweep v p.val; rw [T.sweptJ,T.sweptJ,ho _ ((T.bump p).trans_eq z) _ rfl]; unfold taste; rw [h ⟨_,T.purity p⟩]
       rw [T.swept u (not_not.mp H),T.swept v (not_not.mp H)]
lemma rightHaar (p:T.Stable→ G.El): MeasurePreserving (fun u:T.Free→G.El=>T.dell (T.cite p u)) (Gem G T.Free) (Gem G T.Free):=by
     let s:=T.sweep (T.cite p 1); let f:=fun i:T.Free=> fun k:G.El=> s (R.inn i)*k*(s (R.out i))⁻¹
     have he(u:T.Free→G.El): T.dell (T.cite p u)=fun i=> f i (u i):=by
        funext i; rw [dell,dress,T.kept, T.sweepZ (T.cite p u) (T.cite p 1) (fun p=>by simp)]
     simp_rw [he]; exact measurePreserving_pi _ _ (fun i=> (measurePreserving_mul_right _ _).comp (measurePreserving_mul_left _ _))
lemma dellHaar : MeasurePreserving T.dell (Gem G D) (Gem G T.Free):=by
     have hu:Measurable T.dell:= (T.dellC (K:=G.El)).measurable
     refine ⟨hu,?_⟩; rw [← T.citeHaar.map_eq,Measure.map_map hu T.citeHaar.measurable]
     ext s hs; rw [Measure.map_apply (hu.comp T.citeHaar.measurable) hs,Measure.prod_apply (hs.preimage (hu.comp T.citeHaar.measurable))]
     have he (x:T.Stable→G.El): (Gem G T.Free) ((Prod.mk x) ⁻¹' ((T.dell ∘ (fun u=>T.cite u.1 u.2)) ⁻¹' s))=(Gem G T.Free) s:=
         (T.rightHaar x).measure_preimage hs.nullMeasurableSet
     simp_rw [he]; simp
lemma drapeHaar (H:R.Stand B): MeasurePreserving (T.drapeX (K:=G.El) H) (Gem G T.Free) (Gem G H.Free):=by
      have hu : Measurable (T.drapeX (K:=G.El) H) := (T.delegates H).measurable
      refine ⟨hu,?_⟩; rw [← T.dellHaar.map_eq,Measure.map_map hu T.dellHaar.measurable]; rw [show (T.drapeX H) ∘ T.dell=H.dell from funext fun u:D→G.El=> H.alike T u]; exact H.dellHaar.map_eq
end Score.Stand
end
end YM.OPE.Cascade
