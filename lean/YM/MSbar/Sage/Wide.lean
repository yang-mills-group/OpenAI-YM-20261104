import YM.MSbar.Heath.Charts
import YM.MSbar.Trust.Spilling

/-! # Support-local finite volume to *analytic on the extension* -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V U' V':Config G n}{x:Site n}{R:Rep G n}{σ C T a v δ w:ℝ}
open Finset
open RG.PathData
variable {Y X: Support n}{k M:ℕ}
-- Thickening stencil perimeter to callers. Unconnected shape cost also imported.
def Spine (Y:Support n) (U V:Config G n):=∀ D:Support n,Disjoint D Y → Agrees D U V
structure Place (Y:Support n)(M:ℕ)(U U' V V':Config G n)(t:ℝ) : Prop where
    old : Spine Y U V
    afterX : Spine Y U' V'
    source : Agrees (halo (2*M) Y) U U'
    sinks : Agrees (halo (2*M) Y) V V'
    seals_old : Healthy t (halo (2*M) Y) U
    seals_new : Healthy t (halo (2*M) Y) V
lemma spine_in (h: ∀ e:Edge (Site n),e.1 ∉ Y→ U e= V e) : Spine Y U V:=fun D hD e he he' => h e (fun h=> disjoint_left.mp hD he h)
-- exact channels rotate point and Y list together. Keep bars.
def harp (s:Signed)(Y:Support n) := Y.image (turnSites s 0).symm
variable {t:ℝ}
lemma place_oriented (h:Place Y M U U' V V' t)(s:Signed): Place (harp s Y) M (pull s 0 U) (pull s 0 U') (pull s 0 V) (pull s 0 V') t:=by
   let J:= harp s Y; let a:=turnSites s (0:Site n)
   have hp {U V:Config G n}(ht:Spine Y U V):Spine J (pull s 0 U) (pull s 0 V):= by
       intro D h; apply agrees_pull; apply ht; refine disjoint_left.mpr ?_; intro j hj hV; obtain ⟨i,hi,rfl⟩:=mem_image.mp hj; exact disjoint_left.mp h hi (mem_image.mpr ⟨a i,hV,a.symm_apply_apply i⟩)
   have he a': (halo a' J).image a=halo a' Y:=by
       ext j; constructor
       · intro h; obtain ⟨i,hi,rfl⟩:=mem_image.mp h; obtain ⟨x,hx,H⟩:= halo_spec.mp hi; obtain ⟨k,hk,e⟩:= mem_image.mp hx; rw [← e] at H; apply halo_spec.mpr; refine ⟨_,hk,?_⟩
         exact le_trans (le_of_eq (show separation k (a i)= separation ((turnSites s 0).symm k) i from by rw [← (turn_sep s 0 ((turnSites s 0).symm k) i),Equiv.apply_symm_apply])) H
       intro hi; obtain ⟨i,hj,hh⟩:=halo_spec.mp hi; apply mem_image.mpr; refine ⟨a.symm j,halo_spec.mpr ⟨a.symm i, mem_image_of_mem _ hj,?_⟩,a.apply_symm_apply j⟩; rw [← turn_sep s (0:Site n), show Push.Local.turnSites s 0 _=i from a.apply_symm_apply i, show Push.Local.turnSites s 0 _=j from a.apply_symm_apply j]; exact hh
   refine ⟨hp h.old,hp h.afterX,agrees_pull s 0 ((he _).symm ▸ h.source),agrees_pull s 0 ((he _).symm ▸ h.sinks),?_,?_⟩
   · exact (healthy_pull s 0 t (halo (2*M) J) U).1 ((he _).symm ▸ h.seals_old)
   exact (healthy_pull s 0 t (halo (2*M) J) V).1 ((he _).symm ▸ h.seals_new)
lemma seep  (hx:x∈halo M Y) (hi: ∀ y∈X, separation x y≤ M) : X⊆halo (2*M) Y:=by
    intro i h; obtain ⟨y,hy,H⟩:=halo_spec.mp hx; refine halo_spec.mpr ⟨y,hy,(separation_triangle y x i).trans ?_⟩; have hz:=hi i h; omega
end YM.MSbar.Heath
