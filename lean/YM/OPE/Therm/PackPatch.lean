import YM.OPE.Therm.Clearance
/-!
# Advance currency to many reads
True spacing in both ends of wind axes. In particular translation of mean-zero
scope includes translation of all queried thresholds, no clipping of seats.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Portolan
open Function Set Filter RG Lattice Wilson MeasureTheory Cells House Cradle
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {n:Side} {G:Gauge} {U V : Config G n}
local notation "𝒞" => Config G n
local notation "η" => prior G n
variable {R:Rep G n}{r q:ℕ}{τ a b t X:ℝ}
lemma issue (T:Tiling n)(i:T.Cell)(d:ℕ)(q:ℕ) : ∃ W:Support n, W ⊆ lease T i d ∧
    (W:Set (Site n)).Pairwise (fun x y=>q+q < separation x y) ∧ gx T d ^4 ≤ W.card*(4*q+1)^4:=by
   let J:= q+q; let H:= lease T i d; let f(W:Support n):=W⊆H∧(W:Set (Site n)).Pairwise (fun x y=> q+q < separation x y)
   let S := {W| f W}; have he:S.Nonempty := ⟨∅,(Finset.empty_subset _),by simp⟩; obtain ⟨W,⟨hw,hW⟩,hV⟩:= Set.exists_max_image S (fun W=> W.card) S.toFinite he; have ht:H⊆ halo J W:=by
      intro x hx; by_contra hy; have hh : x∉W:= fun h=> hy (halo_subset J W h)
      have hp : insert x W∈ S:=by
        have hf {y}(h:y∈W) : J < separation y x:= lt_of_not_ge fun H=> hy (halo_spec.mpr ⟨y,h,H⟩)
        refine ⟨Finset.insert_subset hx hw,?_⟩; intro y hy z hz he; rcases Finset.mem_insert.mp hy with hy|hy<;> rcases Finset.mem_insert.mp hz with hz|hz
        · exact False.elim (he (hy.trans hz.symm))
        · rw [hy,separation_comm]; exact hf hz
        · rw [hz]; exact hf hy
        exact hW hy hz he
      exact ((Finset.card_insert_of_notMem hh).symm ▸ (Nat.lt_add_one W.card) : W.card< (insert x W).card).not_ge (hV (insert x W) hp)
   refine ⟨W,hw,hW, (lease_size T i d).symm.trans_le ((Finset.card_le_card ht).trans ((Corona.halo_size W J).trans ?_))⟩; unfold J; apply le_of_eq; ring
section translates
local notation "F"=> Face (Per n)
variable {X:Finset (Edge (Site n))} {f:Config G n→ℝ}
variable (y:Site n) (z:Site n)
local notation "s"=> (1:Signed)
local notation "b₀"=> (y-z)
local notation "v₀"=> (Push.Local.turnSites s b₀)

def lines (X:Finset (Edge (Site n))) := X.image (twist s b₀)
lemma dist_add (x:Site n): separation z x=separation y (affine s b₀ x) := by
   simp only [affine,Signed.act_one]; rw [sub_eq_add_neg, ← sub_eq_add_neg y z]; conv_rhs => arg 1; rw [show y=z+(y-z) by abel]
   rw [separation_translate]
lemma pages : lines y z (coat q z)= coat q y:=by
   ext i; obtain ⟨i,rfl⟩:= (twist s b₀).surjective i; unfold lines coat; simp only [Finset.mem_image, Equiv.apply_eq_iff_eq,exists_eq_right]; exact (turnAny s b₀ (X:=region q z) (Y:=region q y) (by
      intro x; simp only [Finset.mem_coe]; rw [region_mem,region_mem,dist_add y z]) i).1
private lemma face_turn (i:F): (Face.send s b₀ i).1=(affine s b₀ i.1):= by unfold Face.send Face.lower; simp [atFace,posDir]
lemma essence_slide (Z:Stove.Chart R r a t) (U:𝒞) : essence R r τ q z (pull s b₀ U)=essence R r τ q y U:=by
   let g:= v₀; let V:= pull s b₀ U; let B z:= border R r q z; have hp : B y=(B z).image g:=by
      ext x; obtain ⟨x,rfl⟩:= g.surjective x; simp only [Finset.mem_image, Equiv.apply_eq_iff_eq,exists_eq_right]; exact region_mem.trans ((show separation y (g x) ≤ _↔ separation z x ≤ _ by rw [show separation y (g x)=separation z x from (dist_add y z x).symm]).trans region_mem.symm)
   let S (i:Site n):=schedule q i; let F' :=Face.send s b₀; have hh: V∈ chilly (S z) τ ↔ U∈ chilly (S y) τ:=by
      have he i: i∈ S z↔ F' i∈ S y:= by unfold S schedule; simp only [Finset.mem_filter,Finset.mem_univ,true_and, region_mem,F',face_turn]; rw [dist_add y z]
      have ht i: G.chord (faceValue V i)=G.chord (faceValue U (F' i)):= Face.send_price U i s b₀ G.chord G.chord_inv (fun p q=>G.chord_conj q p)
      constructor
      · intro h i hi; obtain ⟨i,rfl⟩:=Finite.injective_iff_surjective.mp (show Injective F' from Face.injective_send s b₀) i; exact (ht _).symm.trans_le (h i ((he i).2 hi))
      exact fun h i hi=> (ht _).trans_le (h (F' i) ((he i).1 hi))
   unfold essence; change _*tape (S z) _ V= Real.exp (-(∑ x∈B y,_))*tape (S y) _ U; unfold tape; simp_rw [hh]; rw [hp,Finset.sum_image g.injective.injOn]; simp_rw [Z.turn]; rfl
lemma neg_form (f:𝒞→ℝ) (h:Attempt R r τ q y f X): Attempt R r τ q y (fun U=>-f U) X:=by
  refine ⟨h.trunks,fun u v hv=>congr_arg Neg.neg (h.warm u v hv),fun U=> (norm_neg ..).trans_le (h.unitBound U),h.hb.neg,fun U=>?_⟩; simp_rw [neg_mul]; rw [show press X (fun u=> -(f u*essence R r τ q y u)) U= -(press X (fun u=>f u* essence R r τ q y u) U) from integral_neg _,h.lands,neg_zero]
lemma attempt_slides (Z:Stove.Chart R r a t)(h:Attempt R r τ q z f X) : Attempt R r τ q y (fun U=> f (pull s b₀ U)) (lines y z X) := by
   have he: lines y z X ⊆ coat q y:= by rw [← pages y z]; exact Finset.image_subset_image h.trunks
   refine ⟨he, fun U V hu=>?_ ,fun _=> h.unitBound _,h.hb.comp ((continuous_pull ..).measurable),fun U=>?_⟩
   · apply h.warm; intro x hx; simp_rw [WardBin.Wheels.pull_by]; rw [hu (show sendEdge s b₀ x∈ (↑(coat q y) : Set _) from (by rw [← pages y z]; exact Finset.mem_image_of_mem (twist s b₀) hx))]
   have ht := h.lands (pull s b₀ U); rw [press_turn s b₀ (Y:=lines y z X) (fun i=> by simp [lines])] at ht; simp_rw [essence_slide y z Z] at ht; exact ht
end translates
end YM.OPE.Therm.Portolan
