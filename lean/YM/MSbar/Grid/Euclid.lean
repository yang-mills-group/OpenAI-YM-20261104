import YM.MSbar.Grid.Laws
import YM.MSbar.Dim.Plane

/-! Grid existence in all actual continuous spaces needed for the structural identities.
Period grids separately for equiv comparisons later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Set Filter MeasureTheory Metric Dim
open scoped BigOperators Classical ENNReal Topology
namespace Snap
variable {M N:Type*} [AddCommGroup M] [AddCommGroup N] [MeasurableSpace M] [MeasurableSpace N]
    [TopologicalSpace M] [TopologicalSpace N] {μ:Measure M}{ν:Measure N}

lemma prod (A:Snap M μ)(B:Snap N ν)[SFinite μ][SFinite ν] : Nonempty (Snap (M×N) (μ.prod ν)) := by
    let s (n):= Finset.product (A.layer n) (B.layer n);let g(n : ℕ):=(A.clan n).prod (B.clan n);let f(n)(v:M×N):=(A.snap n v.1,B.snap n v.2);let d(n):=A.δ n*B.δ n
    have he(n:ℕ)(q:M×N):f n ⁻¹' {q}= (A.snap n ⁻¹' {q.1}) ×ˢ (B.snap n ⁻¹' {q.2}):=by ext1 x; simp [f,Prod.ext_iff]
    refine ⟨⟨g,s,d,fun n=>mul_nonneg (A.nonneg n) (B.nonneg n),f,fun n v=> ⟨A.mem ..,B.mem ..⟩,fun n v hv=> ⟨A.sub _ _ (Finset.mem_product.mp hv).1,B.sub _ _ (Finset.mem_product.mp hv).2⟩,?_,?_,?_,?_,fun v=> (A.seq v.1).prodMk_nhds (B.seq v.2)⟩⟩
    · intro K hK; filter_upwards [A.eventually _ (hK.image continuous_fst),B.eventually _ (hK.image continuous_snd)] with i h1 h2 v hv
      change _ ∧ _ at hv; obtain ⟨h,hv⟩:=hv; change v.1∈ _ ∧ v.2∈ _ at hv; exact Finset.mem_product.mpr ⟨h1 ⟨mem_image_of_mem _ h,hv.1⟩,h2 ⟨mem_image_of_mem _ h,hv.2⟩⟩
    · intro K hc; obtain ⟨U,hU,h⟩:=A.cover _ (hc.image continuous_fst); obtain ⟨V,hV,h'⟩:= B.cover _ (hc.image continuous_snd); refine ⟨U ×ˢ V,hU.prod hV,?_⟩
      filter_upwards [h,h'] with n h k i hi; exact ⟨h (mem_image_of_mem Prod.fst (show f n i∈ K from hi)),k (mem_image_of_mem Prod.snd (show f n i∈ K from hi))⟩
    · intro n i hi; rw [he]; exact (A.knows _ _ (Finset.mem_product.mp hi).1).prod (B.knows _ _ (Finset.mem_product.mp hi).2)
    intro n i hi; rw [he,Measure.prod_prod,A.plays _ _ (Finset.mem_product.mp hi).1,B.plays _ _ (Finset.mem_product.mp hi).2]; exact (ENNReal.ofReal_mul (A.nonneg n)).symm

lemma lifts (A:Snap M μ)(V:M ≃+ N)(u:Continuous V)(v:Continuous V.symm)(b:Measurable V.symm)(h:MeasurePreserving V μ ν): Nonempty (Snap N ν):=by
    let s (n):= (A.layer n).image V;let g(n) := (A.clan n).comap V.symm.toAddMonoidHom;let f(n)(x:N):= V (A.snap n (V.symm x))
    have hx(n:ℕ)(x:N): f n ⁻¹' {x}=V.symm ⁻¹' (A.snap n ⁻¹' {V.symm x}):= by ext; simp [f]; exact V.toEquiv.apply_eq_iff_eq_symm_apply
    have hz(n:ℕ)(x:N):x∈s n ↔ V.symm x∈ A.layer n:=by unfold s; rw [Finset.mem_image]; constructor; rintro ⟨y,hy,rfl⟩; rwa [V.symm_apply_apply];exact fun h=> ⟨_,h,V.apply_symm_apply ..⟩
    have hm(n:ℕ)(x:N)(h:x∈s n):MeasurableSet (f n ⁻¹' {x}):= hx n x ▸ b (A.knows _ _ ((hz n x).mp h))
    refine ⟨⟨g,s,A.δ,A.nonneg,f,fun i y=>by change V.symm (V _ )∈ A.clan i; rw [V.symm_apply_apply]; exact A.mem ..,fun n i hv=> (A.sub _ _ ((hz n i).mp hv)),?_,?_,hm,fun n i hi=>?_,fun i=>?_⟩⟩
    · intro K h; filter_upwards [A.eventually _ (h.image v)] with n h i hi; exact (hz n i).mpr (h ⟨mem_image_of_mem _ hi.1,hi.2⟩)
    · intro K h; obtain ⟨Y,hY,h'⟩:= A.cover _ (h.image v); refine ⟨V '' Y,hY.image u,?_⟩; filter_upwards [h'] with n h i hi
      refine ⟨V.symm i,h (mem_preimage.mpr ⟨f n i,hi,V.symm_apply_apply ..⟩),V.apply_symm_apply ..⟩
    · rw [← h.map_eq,Measure.map_apply h.measurable (hm n i hi),hx]; rw [show V ⁻¹' (V.symm ⁻¹' (A.snap n ⁻¹' {V.symm i}))= A.snap n ⁻¹' {V.symm i} from (by ext; simp)]
      apply A.plays; exact (hz n i).mp hi
    rw [← V.apply_symm_apply i]; simpa [f,comp_def] using ((u.tendsto (V.symm i)).comp (A.seq _))
end Snap
end YM.MSbar.Loops
