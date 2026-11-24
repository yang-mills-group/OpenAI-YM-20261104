import YM.FormalBulk08.Lotus.Rows

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Bloch Filter Set Function
open scoped BigOperators Classical ENNReal Topology
variable {I J : Type*} {η C : ℝ} (n : Side)

lemma rink_bill (R : Row I J) (x : Tor n I) (y : Tor n J) (h : 0≤η):
    rinkshine η n x y * ‖R.acts n x y‖ₑ ≤ ∑' v, if y.1=x.1+wrap n v then shine η (size v)* ‖R x.2 y.2 v‖ₑ else 0 := by
   unfold Row.acts; change _ * ‖∑' v:Cover, (if y.1=x.1+wrap n v then _ else (0:ℝ))‖ₑ ≤ _
   refine (mul_le_mul_right enorm_tsum_le_tsum_enorm _).trans ?_; rw [←ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v; split_ifs with hv
   · unfold rinkshine; rw [show y.1-x.1= wrap n v by rw [hv];simp]; exact mul_le_mul_left (shine_le _ h (skirt n v)) _
   simp
lemma trundle [Fintype I] [Fintype J] (R : Row I J) (h : R.strip η C) (hc : 0≤C) (hs : 0≤η) :
   Hill (rinkshine η n) (R.acts n) ((Fintype.card J)*C) ((Fintype.card I)*C) := by
   refine ⟨by positivity,by positivity,fun x=>?_,fun y=>?_⟩
   · refine (ENNReal.tsum_le_tsum fun y=> rink_bill n R x y hs).trans ?_; rw [ENNReal.tsum_prod', ENNReal.tsum_comm,←dust_cost J C]; apply ENNReal.tsum_le_tsum; intro i; rw [ENNReal.tsum_comm];simpa [eq_comm] using strip_count R h x.2 i
   refine (ENNReal.tsum_le_tsum fun x=> rink_bill n R x y hs).trans ?_; rw [ENNReal.tsum_prod',ENNReal.tsum_comm,←dust_cost I C];apply ENNReal.tsum_le_tsum; intro i; rw [ENNReal.tsum_comm]; simpa [←sub_eq_iff_eq_add] using strip_count R h i y.2

-- widening gates easily financed from d
lemma room (F : Reach I) (G : Reach J) (c : I → J → ℕ)
    (he : ∀ x y v w,G.d v w ≤ c x v+c y w+ F.d x y) (s : ℝ) (hs : 0≤s) {r : ℕ} (v : chain I r) (w : chain J r) :
    shine s (wide G w) ≤ shine s (wide F v)*∏ i, shine s (c (v i) (w i)) := by
   have hh : wide G w ≤ wide F v+∑ i,c (v i) (w i) := by
      apply known_wide; intro i j; by_cases h:i=j
      · subst i; rw [G.self]; omega
      have hv:=he (v i) (v j) (w i) (w j); have ho:= reached F v i j; have h':=Finset.single_le_sum (f:=fun k=>c (v k) (w k)) (s:= Finset.univ.erase i) (fun _ _=>Nat.zero_le _) (show j∈ Finset.univ.erase i by simp [Ne.symm h]);rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i)];omega
   apply (shine_le _ hs hh).trans; rw [shine_add]
   have hp (t : Finset (Fin r)) : shine s (∑ i∈t,c (v i) (w i)) = ∏ i∈t,shine s (c (v i) (w i)) := by
      induction t using Finset.induction with
      | empty=> simp [shine]
      | insert=>simp_all [shine_add]
   rw [hp]

def bridge (I J : Type*) (s : ℝ) (hs : 0≤s) : Solar (fame I) (fame J) s s where
   capsule := linkshine s
   fare := 1
   good := zero_le_one
   carried := fun w v=>by rw [ENNReal.ofReal_one,one_mul]; exact room (fame I) (fame J) (fun x y=>capD y.1 x.1) (fun x y v w=> by have h := cap_travel v.1 x.1 y.1;have e:=cap_travel v.1 y.1 w.1; rw [cap_turn y.1 w.1] at e;change capD _ _ ≤ _+capD x.1 y.1; omega) _ hs w v
def pier (I J : Type*) (s : ℝ) (hs : 0≤s) : Solar (lake n I) (lake n J) s s where
   capsule := rinkshine s n
   fare := 1
   good := zero_le_one
   carried := fun w v=>by rw [ENNReal.ofReal_one,one_mul]; exact room (lake n I) (lake n J) (fun x y=>skit n (y.1-x.1)) (fun x y v w=> by have h:=skit_travel n v.1 x.1 y.1; have e:=skit_travel n v.1 y.1 w.1; rw [skit_sub n y.1 w.1] at e;change skit _ _ ≤ _ + skit n (x.1-y.1);omega) _ hs w v
end YM.FormalBulk08.Lotus
