import YM.SchemeConversionRG11.FirstW.Hart.Summon
/-! Filtering linear algebra without additional norm diamonds. When asserting finite asymptotic of a vector, all linear probes (no change of witness per phase).
No continuity at infinite horizon. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Lattice Pert Align Topology Set Submodule
open scoped BigOperators Classical
variable {I U V Z : Type*} [AddCommGroup U] [AddCommGroup V] [Module ℝ U] [Module ℝ V]
abbrev Low (U : Type*) [AddCommGroup U] [Module ℝ U] := U→ₗ[ℝ]ℝ
def Helen {E : Type*} [TopologicalSpace E] (f : ℕ→E) := ∃ x,Tendsto f atTop (𝓝 x)
def Book (f : ℕ→U) := ∀ a : Low U,Helen (fun i=>a (f i))
def Court (f : ℕ→U) := ∀ a : Low U,∃ C>0,∀ᶠ i in atTop, ‖a (f i)‖≤C
def Level (f : ℕ→U) := ∀ a : Low U,Tendsto (fun i=>a (f i)) atTop (𝓝 0)
variable {a b : ℕ→U}
lemma Book.plus (h : Book a) (p : Book b) : Book (a+b) := by intro B; obtain ⟨x,h⟩:=h B; obtain ⟨y,p⟩:=p B; exact ⟨x+y, by simpa only [Pi.add_apply,map_add] using h.add p⟩
lemma Book.sub (h : Book a) (p : Book b) : Book (a-b) := by intro B; obtain ⟨x,h⟩:=h B; obtain ⟨y,p⟩:=p B; exact ⟨x-y, by simpa only [Pi.sub_apply,map_sub] using h.sub p⟩
lemma Book.mul (h : Book a) (g : ℕ→ℝ) (p : Helen g) : Book (fun i=>g i • a i) := by intro B; obtain ⟨x,h⟩:=h B; obtain ⟨y,p⟩:=p; exact ⟨y*x,by simpa only [map_smul,smul_eq_mul] using p.mul h⟩
lemma Book.map (L : U→ₗ[ℝ] V) (h : Book a) : Book (fun i=>L (a i)) := fun p => h (p ∘ₗ L)
lemma Court.plus (h : Court a) (p : Court b) : Court (a+b) := by
  intro B; obtain ⟨X,hx,h⟩:=h B; obtain ⟨Y,hy,p⟩:=p B
  exact ⟨X+Y, add_pos hx hy,(h.and p).mono fun i hi=> by simp only [Pi.add_apply,map_add]; exact (norm_add_le ..).trans (add_le_add hi.1 hi.2)⟩
lemma Court.map (L : U→ₗ[ℝ] V) (h : Court a) : Court (fun i=>L (a i)) := fun p=>h (p∘ₗ L)
lemma Level.plus (h : Level a)(p : Level b): Level (a+b):= fun B=>by simpa only [zero_add,Pi.add_apply,map_add] using (h B).add (p B)
lemma Level.sub (h : Level a)(p : Level b): Level (a-b):= fun B=>by simpa only [sub_zero,Pi.sub_apply,map_sub] using (h B).sub (p B)
lemma Level.map (L : U→ₗ[ℝ] V)(h : Level a) : Level (fun i=>L (a i)) := fun p=>h (p ∘ₗ L)
lemma Level.book (h : Level a) : Book a := fun p=> ⟨0,h p⟩
lemma Book.court (h : Book a) : Court a := by
  intro p; obtain ⟨x,h⟩:= h p; have h:=h.norm.eventually (gt_mem_nhds (lt_add_one ‖x‖)); exact ⟨‖x‖+1,by positivity,h.mono fun j hj=>hj.le⟩
lemma Level.oil {u : ℕ→ℝ} (h : Tendsto u atTop (𝓝 0)) (q : Court a): Level (fun i=>u i • a i) := by
  intro p; obtain ⟨C,_,H⟩:=q p; simp only [map_smul,smul_eq_mul]; rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_mul]; apply squeeze_zero' (Eventually.of_forall fun a=>by positivity) (H.mono fun i hi=>mul_le_mul_of_nonneg_left hi (norm_nonneg _)) (by simpa only [norm_zero,zero_mul] using h.norm.mul_const C)
-- dual relation factor. arbitrary test index. finite dim domain.
variable (B : I → Low U) {q : Low U} [FiniteDimensional ℝ U]
lemma transmitted (h : ∀ u:U,(∀ i,B i u=0) → q u=0) : q∈ Submodule.span ℝ (range B) := by
 rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=Submodule.span ℝ (Set.range B)), mem_dualAnnihilator]
 intro x hx
 apply h; intro i; exact (mem_dualCoannihilator _).mp hx _ (subset_span ⟨i,rfl⟩)
lemma offbook (h : ∀ u:U,(∀ i,B i u=0) → q u=0) (hp : ∀ i,Helen (fun j=> B i (a j))) : Helen (fun j=>q (a j)) := by
  have e := transmitted B h
  clear h
  induction e using Submodule.span_induction with
  | mem x hx=> obtain ⟨i,e⟩:=hx; rw [← e]; exact hp i
  | zero=> exact ⟨0,tendsto_const_nhds⟩
  | add x y _ _ i j=> obtain ⟨x,h⟩:=i; obtain ⟨y,p⟩:=j; exact ⟨x+y,h.add p⟩
  | smul r x _ i=> obtain ⟨x,p⟩:=i; exact ⟨r*x,p.const_mul r⟩
lemma subPrice (h : ∀ u:U,(∀ i,B i u=0) → q u=0) (hp : ∀ i,∃ C>0,∀ᶠ j in atTop, ‖B i (a j)‖≤C) : ∃ C>0,∀ᶠ j in atTop, ‖q (a j)‖ ≤ C := by
  have e:= transmitted B h
  clear h
  induction e using Submodule.span_induction with
  | mem x hx => obtain ⟨i,e⟩ :=hx; rw [← e]; exact hp i
  | zero=> exact ⟨1,by norm_num, Eventually.of_forall (fun i=>by simp)⟩
  | add x y _ _ i j => obtain ⟨C,hC,i⟩ :=i; obtain ⟨D,hD,j⟩:=j; refine ⟨C+D,by linarith,(i.and j).mono (fun k h=> ?_)⟩; rw [LinearMap.add_apply]; exact (norm_add_le ..).trans (add_le_add h.1 h.2)
  | smul r x _ ih => obtain ⟨C,hC,H⟩:=ih; refine ⟨‖r‖*C+1,by positivity,H.mono (fun i h=>?_)⟩; erw [LinearMap.smul_apply,norm_smul]; exact (mul_le_mul_of_nonneg_left h (norm_nonneg r)).trans (le_add_of_nonneg_right (by norm_num))
lemma Book.aims (h : Book a) : ∃ u : U,∀ L: Low U, Tendsto (fun i=>L (a i)) atTop (𝓝 (L u)) := by
   let b:= Module.finBasis ℝ U
   choose c hc using fun i: Fin (Module.finrank ℝ U)=> h (b.coord i)
   refine ⟨∑ i,c i • b i,fun L=>?_⟩
   have hw u : L u=∑ i,b.coord i u * L (b i) := by nth_rw 1 [← b.sum_repr u,map_sum]; refine Finset.sum_congr rfl fun i _=> L.map_smul ..
   simp_rw [show ∀ i,L (a i)=_ from fun i=>hw (a i),map_sum,map_smul,smul_eq_mul]; exact tendsto_finsetSum _ fun i _=> (hc i).mul_const _
end YM.RG11.FirstW
