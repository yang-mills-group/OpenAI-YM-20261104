import YangMills.WilsonProof.NativeSupport.YM.MS.Book.Pairs
import YM.MS.Book.Mutual
/-! Formal Heisenberg from Wilsonian unscaled. LPT is normalized including quadratic S₂;
 grid k includes initial. `master` property uses true translated identities. Density f tested
 with all vertices as one action.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book
open Function Filter Set Finset Plane Koszul Cylinder Lab Convolve Native Native.Orient Native.Chart Native.Paint Native.Draft Lattice
open Landau Bare Focus
variable {G:Gauge} {k:ℕ} {A P I : Type} [Fintype I] {h:ℤ} {p:Sector A}
local notation "M"=> Dot G Cover

def actB (B:Bonded p I): (T (Seed A Cover ℂ))→ₗ[ℂ] T (Seed A Cover ℂ):= promote B.Lap
def blocks (B:Bonded p I): T (Seed A Cover ℂ)→ₗ[ℂ] T (Seed A Cover ℂ)→ₗ[ℂ] T (Seed A Cover ℂ):= pairW B.touch
-- bundle link; all formula parity

def tokenL (Z: Op A ℂ) (b:Bool) (p:Sector A): Raw A ℂ →ₗ[ℂ] Raw A ℂ→ₗ[ℂ] Raw A ℂ where
    toFun F:= { toFun := link Z b p F, map_add' := fun _ _=>link_add .. , map_smul' := fun _ _=>link_smul ..}
    map_add' := fun _ _=> LinearMap.ext (fun _=> link_add_left ..)
    map_smul' := fun _ _=> LinearMap.ext (fun _=> link_smul_left ..)

variable (B: Bonded p I)
section use
variable (F H: T (Seed A Cover ℂ))(b: Bool)
lemma uses_lap : ∀ᶠ n in atTop, duty b n (actB B F k)= B.district.BV (duty b n (F k)):= dutyBV_heart B _ _
lemma uses_root : ∀ᶠ n in atTop, duty b n (blocks B F H k)=pairW (tokenL B.district.BV true (field p)) (promote (docket n) F) (promote (duty b n) H) k:= by
    unfold blocks; simp only [paired,promised,map_sum]; filter_upwards [(Finset.eventually_all (antidiagonal k)).mpr (fun i _=> dutyBV_root B (F i.1) (H i.2) b)] with n hn; exact Finset.sum_congr rfl fun i hi=>hn i hi

-- including free interaction order zero until recoded from cover Landau

def masterE := (fun n:ℕ=> (actB B F+ (1/2:ℂ) • blocks B F F) n)
-- transparency set

def steadyE := (fun n:ℕ=> (actB B H+ blocks B F H) n)

def Mut (B:Bonded p I)(F: T (Seed A Cover ℂ)) : Prop:= ∀ k, BulkTest (masterE B F k) 0
def Weightless (X:Bonded p I)(F H: T (Seed A Cover ℂ)): Prop:= steadyE X F H=0
end use
lemma whorled (F: T (Seed A Cover ℂ)) : Mut B F↔ ∀ k, ∀ᶠ n in atTop,(promote B.district.BV (promote (docket n) F)) k + (1/2:ℂ) • pairW (tokenL B.district.BV true (field p)) (promote (docket n) F) (promote (docket n) F) k=0:= by
   unfold Mut BulkTest; simp only [masterE,Pi.add_apply,Pi.smul_apply,map_zero,map_smul,map_add]; apply forall_congr' fun k=>?_;
   apply Filter.eventually_congr; filter_upwards [uses_lap B F true (k:=k),uses_root B F F true (k:=k)] with n ha hn
   change docket n _ + (1/2:ℂ) • docket n _=0 ↔ _; rw [show docket n (actB B F k)=promote B.district.BV (promote (docket n) F) k from ha,show docket n (blocks B F F k)=pairW (tokenL B.district.BV true (field p)) (promote (docket n) F) (promote (docket n) F) k from hn]
lemma scales (F H:T (Seed A Cover ℂ)) : Weightless B F H ↔ ∀ k,∀ᶠ n in atTop, (promote B.district.BV (promote (enters n) H)) k + pairW (tokenL B.district.BV true (field p)) (promote (docket n) F) (promote (enters n) H) k=0:= by
    unfold Weightless steadyE; rw [funext_iff]; refine forall_congr' fun k=>?_;
    change (actB B H k + blocks B F H k=0) ↔ _
    rw [← enterEq ..]; apply Filter.eventually_congr; filter_upwards [uses_lap B H false (k:=k), uses_root B F H false (k:=k)] with n ha hn; exact Iff.of_eq (by rw [map_zero,map_add,show enters n (actB B H k)=promote B.district.BV (promote (enters n) H) k from ha,show enters n (blocks B F H k)= pairW (tokenL B.district.BV true (field p)) (promote (docket n) F) (promote (enters n) H) k from hn])
-- duty decomposition for fine-body

def levels (h:ℤ)(F:Seed A P ℂ)(n:ℕ):= model (n+h) F
lemma level_up (h:ℤ)(F:Seed A Cover ℂ)(n:Side)(b:Bool): promote (duty b n) (levels h F)= rankLevel h (duty b n F):= funext fun _=> enterShim b n _

end YM.MS.Book
