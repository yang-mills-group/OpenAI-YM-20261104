import YM.FormalBulk08.Grail.Nim
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Tensor
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G: Gauge} {I J : Type*} {d h r l:ℕ}

def choir (G:Gauge)(d r:ℕ) : Submodule ℝ (Tensor.T (Snap G d) ℝ r) where
    carrier := {M| Monic M}
    zero_mem':= ⟨fun _ _=>rfl,fun _ _=>rfl⟩
    add_mem' {_x _y} h e := ⟨fun v s=> congr_arg₂ (HAdd.hAdd (α:=ℝ)) (h.1 v s) (e.1 v s),fun u v=> congr_arg₂ (HAdd.hAdd (α:=ℝ)) (h.2 u v) (e.2 u v)⟩
    smul_mem' t _x h:= ⟨fun v s=> congr_arg (t *·) (h.1 v s),fun i j=>congr_arg (t*·) (h.2 i j)⟩

lemma conducted {M: Slate G d r}(h:Monic M)(k:ℕ)(L: Fin r→Snap G d)(a:Fin r→ℕ)
    (he:∑ i,a i< k)(_hu:k≤d+1)(hw:∀ i,throughSlot (L i) (a i)) (hp:∀ m:ℕ,m<k→WardBin.tile (tide M) m=0): M L=0:= by
    let X(i:Fin r)(j:Fin (d-1)): Snap G d:= Pi.single j (L i j)
    rw [show L= fun i=>∑ j,X i j from funext fun i=> (Finset.univ_sum_single _).symm,M.map_sum X]; refine Finset.sum_eq_zero fun j _=> ?_
    by_cases hX:∀ i,(j i).val+2≤a i
    · have hb : Parts.rate j < k:= (Finset.sum_le_sum (fun i _=> hX i)).trans_lt he
      have hh:= Parts.tile_detects (tide M) (tide_symm h.1) j (hp _ hb) (fun i=>L i _)
      apply Complex.ofReal_injective; exact hh.trans (Complex.ofReal_zero).symm -- elaboration
    push Not at hX; obtain ⟨i,hi⟩:= hX; apply M.map_coord_zero i; unfold X; rw [hw i (j i) hi,Pi.single_zero]

lemma series_cap [Fintype J][AddCommGroup I][Module ℝ I](V:I→ₗ[ℝ]ℝ)(F:J→I→ₗ[ℝ]ℝ)(h:∀ x,(∀ i,F i x=0)→ V x=0) : ∃ C:ℝ,0≤C ∧ ∀ x,∀ c, (∀ i, |F i x| ≤ c) → |V x|≤ C*c:= by
   have ht:= mem_span_of_iInf_ker_le_ker (ι:=J) (L:=F) (K:=V) (by
       intro x hx; exact h _ fun i=> show x∈LinearMap.ker (F i) from (Submodule.mem_iInf _).1 hx i)
   obtain ⟨u,hu⟩:= (Submodule.mem_span_range_iff_exists_fun ℝ).mp ht
   refine ⟨∑ i,|u i|,Finset.sum_nonneg fun _ _=> abs_nonneg _, fun x c ht=>?_⟩
   rw [←hu, LinearMap.sum_apply]; rw [Finset.sum_mul]; exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun i _=>le_trans (le_of_eq (abs_mul ..)) (mul_le_mul_of_nonneg_left (ht i) (abs_nonneg _))))

variable (F: Frame G d)
def diagV (i:F.Index): (choir G d r)→ₗ[ℝ]ℝ where
    toFun M:= (pocket F M.val (F.grades i).1 i).re
    map_add' x y:= by
       rw [Submodule.coe_add,bunch]; rfl
    map_smul' c x:= by rw [Submodule.coe_smul_of_tower,stip]; simp
-- ℓ from r directions; flags which need occupy narrow height.
lemma diagram (k:ℕ)(L: Fin r→Snap G d)(a:Fin r→ℕ)(he:∑ i,a i< k)(hu:k≤d+1)(hw:∀ i,throughSlot (L i) (a i))(ha:r≤ d):
   ∃ C:ℝ,0≤C∧ ∀ M: Slate G d r,Monic M→∀ A, (∀ i, (F.grades i).1 <k → (F.grades i).2=r → ‖(Pose.pocket F M (F.grades i).1 i).re‖≤ A) →‖M L‖≤ C*A := by
   let H:=choir G d r; let V: H→ₗ[ℝ]ℝ:={toFun:= fun M=> M.val L,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; let K:=Finset.univ.filter (fun i:F.Index=> (F.grades i).1<k∧ (F.grades i).2=r)
   let Q(i:(K:Set F.Index)) := diagV (r:=r) F i.val; let R(i:K):=diagV (r:=r) F i.val
   have Hg (x) (hx:∀ i,R i x=0): V x=0:= by
     refine conducted (show Monic x.val from x.property) k L a he hu hw (fun m hm=>?_)
     let X:=lent x.val m; have h': Monic x.val:=x.property
     have hh: m≤d:= by omega
     have he: X∈Grade (m,r):= lent_grade h' hh ha
     have hz : F.coords X = F.coords 0:= by
         rw [map_zero]; funext i;
         by_cases hv : (m,r)=F.grades i
         · let j:K:=⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [←hv]; exact ⟨hm,rfl⟩⟩⟩
           change pocket F x.val m i= (0:ℂ); rw [←pocket_real F _ h' hh ha i]; unfold R at hx
           rw [show m=(F.grades i).1 from congr_arg Prod.fst hv, show (pocket F x.val _ i).re= _ from hx j, Complex.ofReal_zero];
         exact F.power_coefficient i hv he
     rw [← lent_pure h' hh ha,show lent x.val m=0 from F.coords.injective hz]; rfl
   obtain ⟨C,hC,H'⟩:= series_cap V R Hg
   exact ⟨C,hC, fun T h A he=>H' (⟨T,h⟩:H) A (fun i=>he i.val (Finset.mem_filter.mp i.property).2.1 (Finset.mem_filter.mp i.property).2.2)⟩
end YM.FormalBulk08.Grail
