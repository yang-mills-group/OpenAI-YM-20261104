import YM.FormalBulk08.Gorge.Lantern
import YM.Laurent.Art

/-! Cover and toric cases, choose SAME size as Width. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Filter Set
open scoped BigOperators Classical ENNReal Topology
variable {r : ℕ}
abbrev Biglot (I : Type*) := Cover × I
abbrev Tor (n : Side) (I : Type*) := Site n × I

def capD (x y:Cover):=size (x-y)
lemma cap_travel (x y z) : capD x z ≤ capD x y+capD y z := by unfold capD; rw [←sub_add_sub_cancel x y z]; exact size_add ..
lemma cap_turn (x y) : capD x y=capD y x:= by unfold capD;rw [←size_neg,neg_sub]
def fame (I : Type*) : Reach (Biglot I):=⟨fun a b=>capD a.1 b.1, fun a=>by simp [capD,size],fun _ _=> cap_turn ..,fun _ _ _=>cap_travel ..⟩
def skit (n : Side) (x : Site n) := size (lift x)
lemma skit_neg (n : Side) (x : Site n) : skit n (-x)= skit n x:= by simp [skit,size,Lattice.lift]
lemma skit_sub (n : Side) (x y : Site n) : skit n (x-y)= skit n (y-x):= by rw [←skit_neg n,neg_sub]
lemma skit_add (n : Side) (x y : Site n) : skit n (x+y) ≤ skit n x+skit n y:=by
   unfold skit size; rw [←Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _=>(ZMod.natAbs_valMinAbs_add_le (x i) (y i)).trans (Int.natAbs_add_le ..)
lemma skit_travel (n : Side) (x y z : Site n) : skit n (x-z) ≤ skit n (x-y)+skit n (y-z):= by rw [←sub_add_sub_cancel x y z]; exact skit_add ..
def lake (n : Side) (I : Type*) : Reach (Tor n I):= ⟨fun a b=> skit n (a.1-b.1),fun a=>by simp [skit,size,Lattice.lift],fun _ _=> skit_sub .., fun _ _ _=> skit_travel ..⟩
lemma skirt (n : Side) (x : Cover) : skit n (wrap n x)≤size x := by
   unfold skit size; refine Finset.sum_le_sum fun i _=>?_
   change (ZMod.valMinAbs ((x i:Per n))).natAbs ≤ _ -- pipe issue
   by_cases h : (x i).natAbs < n.val/2
   · have he : ZMod.valMinAbs ((x i: Per n))=x i:= (ZMod.valMinAbs_spec ..).mpr ⟨rfl,by rw [Set.mem_Ioc]; omega⟩
     rw [he]
   exact (ZMod.natAbs_valMinAbs_le _).trans (by omega)
variable {V I : Type*}
def drip (n : Side) (v : Biglot I) : Tor n I := (wrap n v.1,v.2)
def boil (n : Side) (v : Tor n I) : Biglot I:= (lift v.1,v.2)
@[simp] lemma drip_boil (n : Side) (v : Tor n I) : drip n (boil n v)=v:=by simp [boil,drip]
lemma skirt_wide (n : Side) (v : chain (Biglot I) r) : wide (lake n I) (drip n ∘ v) ≤ wide (fame I) v := known_wide _ _ _ (fun i j=>by
    change skit n (wrap n (v i).1- wrap n (v j).1) ≤ _; rw [←map_sub]; exact (skirt ..).trans (reached (fame I) v i j))
lemma effect (x : Cover) : ∀ᶠ n : Side in atTop, Lattice.lift (wrap n x)=x := by
   simp only [lift_eq_iff,true_and]; rw [eventually_all]; intro i
   filter_upwards [eventually_ge_atTop (α:=Side) ⟨2*(x i).natAbs+1,by omega⟩] with n hn
   change 2*(x i).natAbs+1 ≤ n.val at hn; omega
lemma boil_drip (v : Biglot I) : ∀ᶠ n : Side in atTop, boil n (drip n v)=v := by
   filter_upwards [effect v.1] with n hn; simp [boil,drip,hn]
lemma same_drip (x y : Biglot I) : ∀ᶠ n : Side in atTop, drip n x=drip n y ↔ x=y := by
   filter_upwards [boil_drip x,boil_drip y] with n hx hy; exact ⟨fun h=> hx.symm.trans ((congr_arg (boil n) h).trans hy), fun h=> congr_arg (drip n) h⟩
end YM.FormalBulk08.Lotus
