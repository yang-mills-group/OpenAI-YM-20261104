import YM.MS.Cylinder.Orbit
import YM.CellFourier.Mesh
/-! Absolute lattice ps=identity, no forcing momenta periodic at LPT step. Define bulk
 extension tests by requiring wrap at arbitrarily large (all sufficiently).
 These prove more than the final course w=0 identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder.Lab
open Function Filter Set Finset Koszul Plane
open Lattice
open scoped Topology ContDiff
variable {R A I P : Type*}[CommRing R] {p:Sector A}

lemma larger (z:Cover): ∀ᶠ n:Side in atTop, Lattice.lift (wrap n z)=z := by
    simp_rw [lift_eq_iff, true_and]
    apply eventually_all.mpr; intro i; let M:Side:=⟨(z i).natAbs*2+1, Nat.zero_lt_succ _⟩
    filter_upwards [eventually_ge_atTop M] with n hn; change (z i).natAbs*2+1 ≤ n.val at hn; omega
lemma later (s:Finset Cover): ∀ᶠ n:Side in atTop, Set.InjOn (wrap n) (s:Set Cover):= by
    filter_upwards [(Finset.eventually_all s).mpr (fun x _=> larger x)] with n H; exact fun i hi j hj he=> (H i hi).symm.trans ((congr_arg Lattice.lift he).trans (H j hj))
def shown (n:Side) : Seed A Cover R→ₗ[R] Seed A (Site n) R:= transport (wrap n)
def patched (F H:Seed A Cover R) := ∀ᶠ n in atTop, shown n F=shown n H
def enters (n:Side) : Seed A Cover R→ₗ[R] Row A (Site n) R:= (Stack _ _).subtype.comp (shown n)
def docket (n:Side) : Seed A Cover R→ₗ[R] Row A (Site n) R:= (Stack _ _).subtype.comp (sumHome.comp (shown n))
def duty (b:Bool) (n:Side) : Seed A Cover R→ₗ[R] Row A (Site n) R:= if b then docket n else enters n

def BulkTest (F H:Seed A Cover R) := ∀ᶠ n in atTop, docket n F=docket n H
-- module values with additional proof args
lemma markEq (F H:Seed A Cover R): patched F H↔ F=H:= by
    refine ⟨fun h=>?_, fun h=> Eventually.of_forall (fun x=>h ▸ rfl)⟩
    obtain ⟨s,hs⟩:= obliges (F-H); obtain ⟨n,he,hv⟩:= (h.and (later s)).exists -- adjust
    exact sub_eq_zero.mp (transport_zero (wrap n) hv (F-H) hs (show shown n (F-H)=0 from by rw [map_sub,he,sub_self]))
lemma enterEq (F H:Seed A Cover R): (∀ᶠ n in atTop, enters n F=enters n H)↔ F=H:= by rw [← markEq]; exact ⟨fun h=> h.mono (fun x h=> Subtype.ext h),fun h=> (markEq _ _|>.mp h) ▸ Eventually.of_forall (fun _=>rfl)⟩

variable [Fintype I] (B:Bonded p I) (F H:Seed A Cover R)
lemma soon_heart : ∀ᶠ n in atTop, shown n (B.Lap F)= B.Lap (shown n F) := by obtain ⟨s,hs⟩:=obliges F; exact (later s).mono (fun n h=> B.lap_traces F _ hs h)
lemma soon_root : ∀ᶠ n in atTop, shown n (B.touch F H)= B.touch (shown n F) (shown n H):= by obtain ⟨s,hs,hv⟩:=each_side F H; exact (later s).mono (fun n h=> B.feel _ F H hs hv h)
lemma dutyBV_heart (b:Bool): ∀ᶠ n in atTop, duty b n (B.Lap F)=B.district.BV (duty b n F):= by
   filter_upwards [soon_heart B F] with n h; cases b
   · change (shown n _).val=B.district.BV (shown n _).val; rw [h,B.lap_here]
   change (sumHome (shown n _)).val=B.district.BV (sumHome (shown n _)).val; rw [h,B.l_bulk]
lemma dutyBV_root (b:Bool): ∀ᶠ n in atTop, duty b n (B.touch F H)= link B.district.BV true (field p) (docket n F) (duty b n H):= by
   filter_upwards [soon_root B F H] with n h; cases b
   · change (shown n _).val= _; rw [h,B.t_here]; rfl
   change (sumHome (shown n _)).val= _; rw [h,B.t_bulk]; rfl
end YM.MS.Cylinder.Lab
