import YM.OPE.Therm.Garret
/-!
# Counts for room entropy; move within margins including halo receipts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.House
open Function Filter RG Lattice Wilson MeasureTheory Cells
open scoped BigOperators Classical Topology
variable {n:Side} {G:Gauge}
variable (T:Tiling n) {v u:T.Cell} {x y:Site n} {r q:ℕ}
local notation "γ"=> T.coordinated
local notation "N"=>T.side.val
local notation "#$" => Fintype.card T.Cell
local notation "∆"=> T.chamber

def lease (v:T.Cell)(r:ℕ): Support n:= Finset.univ.filter (fun x=>∀ i,r≤ γ v x i ∧ γ v x i+r≤N)
lemma leased : x∈lease T v r ↔ ∀ i,r≤ γ v x i ∧ γ v x i+r≤N:=by simp [lease]
lemma gesture (h:r≤q) : lease T v q ⊆ lease T v r:= by
   intro x hx; apply (leased T).mpr; intro a; have := (leased T).mp hx a; omega
@[simp] lemma lobby (v:T.Cell): lease T v 0=suite T v:=by ext x; rw [leased,host]; simp [hall]
def gx (i:ℕ):ℕ:= N+1-2*i
lemma lease_size (v:T.Cell) (r:ℕ): (lease T v r).card=(gx T r)^4:=by
   let s:=lease T v r; let F (z:Axis→Fin (gx T r)):Site n:= fun i=>T.starts v i+(↑(r+(z i).val):Per n)
   have he (i: Fin (gx T r)): r+i.val + r≤ N:=by have ht:= i.isLt; unfold gx at ht; omega
   have hc z i: γ v (F z) i = r+(z i).val:=by
      simp only [F,Tiling.coordinated,add_sub_cancel_left]; apply ZMod.val_natCast_of_lt; have hz:= he (z i); have hp:= T.narrow; omega
   have hh : (Finset.univ.image F) = s:=by
      ext x; constructor
      · intro hx; obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hx; apply (leased T).mpr; intro i; rw [hc]; refine ⟨Nat.le_add_right .., he _⟩
      intro h; have hp:= (leased T).mp h; have ht (i):γ v x i-r < gx T r:=by have hh:= hp i; unfold gx; omega
      let z:= fun i=> (⟨_,ht i⟩:Fin (gx T r)); apply Finset.mem_image.mpr; refine ⟨z,Finset.mem_univ _,?_⟩; ext1 i; dsimp only [F,z]; rw [Nat.add_sub_of_le (hp i|>.1)]; exact T.indent v x i
   change s.card=_; rw [← hh,Finset.card_image_of_injective _ (show Injective F from fun i j he=>funext fun a=> Fin.ext (Nat.add_left_cancel ((hc i a).symm.trans ((congr_arg (γ v · a) he).trans (hc j a)))))]; simp [Axis]
lemma hall_size (v:T.Cell): (suite T v).card=(N+1)^4:= by simpa [gx] using lease_size T v 0
lemma hall_leased (h:x∈lease T v r) : x∈suite T v:=by rw [← lobby]; exact gesture T (Nat.zero_le _) h
lemma halls_face_count (v:T.Cell):
   (Finset.univ.filter fun i:Face (Per n)=> touched i⊆ suite T v).card≤ (N+1)^4 * Fintype.card PlaqAxes:=by
   calc
      _ ≤ ((suite T v) ×ˢ Finset.univ (α:=PlaqAxes)).card := Finset.card_le_card fun i h => Finset.mem_product.mpr ⟨(show touched i ⊆ suite T v from (Finset.mem_filter.mp h).2) (Work.E01.base_touched i),Finset.mem_univ _⟩
      _ = _ := by rw [Finset.card_product,Finset.card_univ,hall_size]
section
variable (hv:T.kind=.site)
include hv
lemma seated (h:1≤ r) : x∈lease T v r ↔ x ∈ T.margin v r:= by
   have hx : T.kind.shift=0:= by rw [hv]; rfl
   rw [leased T]; change _ ↔ x∈T.chamber v∧ _; rw [interior T hv]; simp only [hx, add_zero]
   constructor
   · intro hX; refine ⟨fun i=> ?_,hX⟩; specialize hX i; omega
   exact (·.2)
lemma soldApart (h:1≤r) : Pairwise (fun i j=> Disjoint (lease T i r) (lease T j r)):=fun i j hi=> Finset.disjoint_left.mpr (fun x hx hy=> hi ((T.which_chamber ((seated T hv h).mp hx).1).symm.trans (T.which_chamber ((seated T hv h).mp hy).1)))
lemma deeds {x y:Site n}(h:1≤ r)(he:separation x y< r)(hx:x∈lease T v r):y ∈ ∆ v:=by
   have hh:= deed T v (r-1) (by rw [Nat.sub_add_cancel h]; exact (seated T hv h).mp hx); exact hh (halo_spec.mpr ⟨x,Finset.mem_singleton_self _,by omega⟩)
-- inner move remains leased with reduced margin
lemma tending
    (he:x∈lease T v (r+q))(h: separation x y≤ q) : y∈ lease T v r:= by
   rw [leased]; intro i; obtain ⟨hp,hP⟩:= (leased T).mp he i; let a:= lift (y-x); have ha: (a i).natAbs ≤ q:= (component_le (y-x) i).trans ((separation_comm y x).trans_le h); let j:ℤ:= γ v x i + a i; have hj : r ≤ j:= by unfold j; omega
   have h₀ : 0≤ j:= (Nat.cast_nonneg _).trans hj; have hy:j.toNat + r≤ N:=by unfold j at *; omega
   have ht :γ v y i=j.toNat:=by
      unfold Tiling.coordinated; rw [show y i -T.starts v i=↑(j.toNat) from ?_,ZMod.val_natCast_of_lt (by have ht:=T.narrow; omega)]; rw [← Int.cast_natCast,Int.toNat_of_nonneg h₀]; have hx : (a i : Per n)=y i-x i:= congr_fun (wrap_lift (y-x)) i; rw [show j= _ from (rfl:j=↑(γ v x i)+a i),Int.cast_add,hx,Int.cast_natCast]; simp [Tiling.coordinated,Per]
   rw [ht]; exact ⟨by omega,hy⟩
lemma tour (v:T.Cell)(r:ℕ)(h:1≤r): x∈lease T 0 r ↔ T.copyMap v x∈lease T v r:=by rw [seated T hv h,seated T hv h,T.reflected_margin]

def vacant (r:ℕ) := Finset.univ \ Finset.univ.biUnion (fun i=> lease T i r)
lemma gap_lot (h:1≤r) : (vacant T r).card= #$ *(N^4 - gx T r^4):=by
   have hh : Fintype.card (Site n)= #$ * N^4:=by rw [site_card,site_card,T.units.exact_size,mul_pow];
   unfold vacant; rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ, Finset.card_biUnion (s:=Finset.univ) (t:=fun i=>lease T i r) (by intro i hi j hj hx; exact soldApart T hv h hx),hh,Nat.mul_sub]; simp_rw [lease_size]; simp
lemma outsideFee (h:1≤r) : ((vacant T r).card:ℝ) ≤ (#$:ℝ)*(8 * r * N^3):=by
   let j:=gx T r; let i:=N; have hx :j≤ i:= by unfold j i gx; omega
   have ht:j+2*r ≥ i:= by unfold j i gx; omega;
   rw [gap_lot T hv h,Nat.cast_mul,Nat.cast_sub (Nat.pow_le_pow_left hx _)]; push_cast; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); change (i:ℝ)^4 - (j:ℝ)^4 ≤ 8*r*(i:ℝ)^3
   have hh : (i:ℝ) - j ≤ 2*r:=by rw [sub_le_iff_le_add']; exact_mod_cast ht; -- add order?
   have hj : (j:ℝ) ≤ i:= by exact_mod_cast hx
   have hJ : (0:ℝ) ≤ j:= Nat.cast_nonneg _; have hN : (0:ℝ) ≤ i:= Nat.cast_nonneg _
   have hP: ∀ n:ℕ,(j:ℝ)^n ≤ (i:ℝ)^n:= pow_le_pow_left₀ hJ hj
   let P :ℝ:= (i:ℝ)^3+(i:ℝ)^2*j+i*(j:ℝ)^2+(j:ℝ)^3; have h1 : P ≤ 4*(i:ℝ)^3:=by unfold P; linarith only [mul_le_mul_of_nonneg_left hj (sq_nonneg (i:ℝ)),mul_le_mul_of_nonneg_left (hP 2) hN,hP 3]
   calc
      _=((i:ℝ)-j)*P := by unfold P; ring
      _≤ _ := (mul_le_mul hh h1 (by unfold P; positivity) (by positivity)).trans_eq (by ring)
lemma seamCount : ((seam T).card:ℝ) ≤ 4* (#$:ℝ)*(16*N^3):=by
   have hh : (seam T)⊆(vacant T 2)×ˢ (Finset.univ:Finset Axis):=by
       intro i hi; simp only [Finset.mem_product,vacant,Finset.mem_univ, and_true,Finset.mem_sdiff,true_and,Finset.mem_biUnion,not_exists]; intro v h
       have hz := deeds T hv (r:=2) one_le_two (lt_of_le_of_lt (Work.E01.sep_step_le i.1 i.2) (by norm_num)) h
       exact ((wraps T).mp hi v) (books T (linn.mpr ⟨((seated T hv (one_le_two)).mp h).1,hz⟩))
   have hZ : (2:ℝ) ≥ 1:=by norm_num
   refine (Nat.cast_le.mpr (Finset.card_le_card hh)).trans ?_; rw [Finset.card_product,Finset.card_univ,show Fintype.card Axis=4 from Fintype.card_fin _]; push_cast; have he:= outsideFee T hv (one_le_two); push_cast at he; linarith only [he]
end
end YM.OPE.Therm.House
