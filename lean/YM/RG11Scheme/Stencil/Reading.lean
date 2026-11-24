import YM.RG11Scheme.Stencil.Currents

/-! Finite supported dual read entries and link evaluation kernels. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Stencil
open Filter Set Function Lattice Mesh
open scoped BigOperators Classical
variable {G:Gauge} {X : Type} {E : Type*} {F : Type*} {Y:Type*} {Z : Type*}
-- finite dependencies

def taps (f:(X→E)→F) (s : Finset X) := ∀ A B:X→ E, (∀ l∈s,A l=B l)→ f A=f B
def brief (f:(X→E)→F) := ∃ s, taps f s
lemma taps.mono {s t:Finset X} {f:(X→E)→F} (h:taps f s)(hp:s⊆t) : taps f t := fun A B e=> h A B (fun l hl=>e l (hp hl))
lemma brief.one (l:X) : brief (fun z:X→E=> z l) := ⟨{l},fun _ _ hp=>hp l (Finset.mem_singleton_self l)⟩
lemma brief.still (f:F) : brief fun _:X→E=> f := ⟨∅,fun _ _ _=>rfl⟩
lemma brief.then {f:(X→E)→F} (h:brief f) (g:F→Y) : brief fun v=>g (f v) := ⟨_,fun a b he=> congrArg g (h.choose_spec a b he)⟩
lemma brief.combine {f:(X→E)→F} {g:(X→E)→Y} (h:brief f) (q:brief g) (v:F→Y→Z) : brief fun x=> v (f x) (g x) := ⟨h.choose∪q.choose,fun _ _ he=> congrArg₂ v (h.choose_spec _ _ (fun i hi=>he i (Finset.mem_union.mpr (.inl hi)))) (q.choose_spec _ _ (fun i hi=>he i (Finset.mem_union.mpr (.inr hi))))⟩
lemma current_vanish {A:Dual G} {s} (ht:taps A s) (p:link) (hp:p∉s) : current A p=0 := by
   ext c; rw [current_one]
   have he : A (key (Maxwell.unitColor G c) p) = A 0 := ht _ 0 (fun l hl=> if_neg (show l≠p from fun e=> hp (e ▸ hl)))
   exact he.trans A.map_zero
lemma current_finite {A:Dual G} (ht:brief A) : (current A).HasFiniteSupport := Set.Finite.subset (Finset.finite_toSet ht.choose) (fun p hp=> show p∈ht.choose from Classical.byContradiction (fun h=> hp (current_vanish ht.choose_spec p h)))
lemma select (U:Bond G) (s:Finset link) (l:link) (hl:l∈s) : (∑ u∈s, key (U u) u) l=U l := by
   simp_rw [Finset.sum_apply, key, eq_comm (a:=l)]
   simp [hl]
lemma tapping {A:Dual G} {s : Finset link} (h:taps A s) (U) : A U = ∑ p∈s, inner ℝ (U p) (current A p) := by
   calc _ = A (∑ u∈s, key (U u) u) := (h U _ (fun l hl=>(select U s l hl).symm))
        _ = _ := by rw [map_sum]; simp_rw [current_eval]

lemma cupboard {A:Dual G} (h:brief A) (U) : A U = ∑' p:link, inner ℝ (U p) (current A p) := (tapping h.choose_spec U).trans ((tsum_eq_sum (s:=h.choose) (fun p hp=> by rw [current_vanish h.choose_spec p hp,inner_zero_right])).symm)
lemma ray_emits {A:Dual G} {s} (h:taps A s) : ray A=∑ u∈s,node (current A u) u := by
   funext l; ext d
   rw [Finset.sum_apply,WithLp.ofLp_sum,Finset.sum_apply,ray_one,tapping h]
   refine Finset.sum_congr rfl (fun i _=>?_)
   by_cases e:i.2=l.2
   · unfold node; rw [if_pos e,if_pos e.symm]
     rw [←opposite (l.1-i.1),neg_sub]; rw [real_inner_smul_left,real_inner_comm,Pert.Align.to_color]; rfl
   unfold node; rw [if_neg e,if_neg (Ne.symm e), inner_zero_left]; exact rfl
lemma sym_current (A B : Dual G) (hA:brief A) (_hB:brief B) : A (ray B) = B (ray A) := by
   rw [ray_emits hA.choose_spec,map_sum]; rw [tapping hA.choose_spec]
   refine Finset.sum_congr rfl (fun i _=> ?_)
   rw [real_inner_comm, ray_eval] -- simp?
def point_ad (u:G.Color) : Bond G→ₗ[ℝ] Bond G := LinearMap.pi fun i=> G.ad u ∘ₗ LinearMap.proj i
lemma adj_current {A:Dual G}(u:G.Color) (p:link) : current (A ∘ₗ point_ad u) p= -G.ad u (current A p) := by
   apply ext_inner_left ℝ; intro v;rw [current_eval,LinearMap.comp_apply]
   have he : point_ad u (key v p) = key (G.ad u v) p:= funext fun i=>by unfold point_ad key; rw [LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.proj_apply]; split_ifs<;> simp
   rw [he,←current_eval, G.ad_skew,inner_neg_right]
lemma adj_taps {A:Dual G} {s} (h:taps A s)(v:G.Color): taps (A ∘ₗ point_ad v) s := fun U V he=> h (point_ad v U) (point_ad v V) (fun z hz=> congrArg (fun x=> G.ad v x) (he z hz))
lemma reaches {A:Dual G} {s} (h:taps A s) (v:G.Color) : ray (A ∘ₗ point_ad v) = -point_ad v (ray A) := by
   rw [ray_emits h,ray_emits (adj_taps h v),map_sum,←Finset.sum_neg_distrib]
   refine Finset.sum_congr rfl (fun i hi=>?_);rw [adj_current]; funext l; unfold node
   change _= -(G.ad v _)
   split_ifs with he; · simp [he]
   simp [he]

lemma rotation_sum (A B : Dual G) (hA:brief A) (hB:brief B) (v:G.Color) : A (point_ad v (ray B))+ B (point_ad v (ray A))=0 := by
   rw [show A _=(A ∘ₗ point_ad v) (ray B) from rfl,sym_current _ _ ⟨_,adj_taps hA.choose_spec v⟩ hB,reaches hA.choose_spec,map_neg,neg_add_cancel]
end YM.RG11Scheme.Stencil
