import YM.MS.Book.Chants
/-!
# Exact operators projected on indexed coefficients

`Weightless` means zero under BV, not that correlation vanished; prove the
  latter separately. To avoid ∆^2 definitions on infinite translated function
 spaces, use Lens. Not assuming ghosts satisfy spectrum. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book
open Function Filter Set Finset Plane Koszul Cylinder Lab Convolve Lattice
variable {A P I : Type}[Fintype I] {p:Sector A}{B:Bonded p I}
variable (F H: T (Seed A Cover ℂ))
def modulo (B:Bonded p I)(f:T (Raw A ℂ)): T (Raw A ℂ)→ₗ[ℂ] T (Raw A ℂ):= promote B.BV +pairW (tokenL B.BV true p) f

lemma read_dual (b:Bool) (k:ℕ) : ∀ᶠ n in atTop, duty b n (steadyE B F H k) = modulo B.district (promote (docket n) F) (promote (duty b n) H) k:= by
   filter_upwards [uses_lap B H b (k:=k), uses_root B F H b (k:=k)] with n ha hn; change duty b n (_+_)=_; rw [map_add, ha, hn]; rfl
local notation "L" => tokenL B.BV true p
def tokM (B:Bonded p I)(F:T (Raw A ℂ)): T (Raw A ℂ):= promote B.BV F + (1/2:ℂ) • pairW (tokenL B.BV true p) F F
lemma tokH (F H:T (Raw A ℂ))(k:ℕ)(he: ∀ i, Symm p (F i))(hv:∀ i,Pure p false (F i))(hs:∀ i,Symm p (H i)): (modulo B F (modulo B F H)) k= -(pairW L (tokM B F) H k) := by
    let D:= promote (B.BV : Op A ℂ); let T0:= pairW L; let W:=T0 F (T0 F H); let Y:∀ f g h:A, Nat:=fun _ _ _=>0
    have hu : (D (D H)) k=0:= B.costs.quits (hs k)
    have hz i j:= (B.costs (R:=ℂ)).anti_j (hv i) (he i) (hs j)
    change (D (D H+T0 F H)+ T0 F (D H+T0 F H)) k= -(T0 (D F+(1/2:ℂ) • T0 F F) H k)
    simp_rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,Pi.add_apply, Pi.smul_apply]; rw [hu];
    have hd : (D (T0 F H) k+T0 F (D H) k)+ T0 (D F) H k=0:= by
       change B.BV (∑ i∈antidiagonal k,L (F i.1) (H i.2)) + (∑ i∈antidiagonal k,L (F i.1) (B.BV (H i.2))) + (∑ i∈antidiagonal k,L (B.BV (F i.1)) (H i.2)) =0
       simp_rw [map_sum,← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun i _=> hz i.1 i.2
    have hu' : W k+W k+ T0 (T0 F F) H k=0:= by
        let M a b c:= L (F a) (L (F b) (H c))
        have hp : W k= ∑ i∈antidiagonal k,∑ j∈antidiagonal i.2,M i.1 j.1 j.2:= by unfold M W T0; rw [paired]; simp_rw [paired,map_sum]
        rw [hp,Convolve.associate]
        nth_rw 2 [show (∑ i∈antidiagonal k,∑ j∈antidiagonal i.1,M j.1 j.2 i.2)=∑ i∈antidiagonal k,∑ j∈antidiagonal i.1,M j.2 j.1 i.2 from Finset.sum_congr rfl (fun i _=> (Finset.Nat.sum_antidiagonal_swap (n:=i.1) (f:=fun j=> M j.1 j.2 i.2)).symm)]
        unfold T0; simp_rw [paired,map_sum,LinearMap.sum_apply,← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun d _=> Finset.sum_eq_zero fun i _=> (B.costs).mix_j (hv _) (hv _) (he _) (he _) (hs _)
    have hp := congr_arg ((1/2:ℂ) • ·) hu'; simp only [smul_add,smul_zero] at hp; rw [← add_smul] at hp; unfold W at hp; rw [show (1/2:ℂ)+(1/2:ℂ)=1 by norm_num,one_smul] at hp; linear_combination (norm:=abel) hd + hp
lemma opaqued (k:ℕ) : ∀ᶠ n in atTop, docket n (masterE B F k)= tokM B.district (promote (docket n) F) k:= by
    filter_upwards [uses_lap B F true (k:=k),uses_root B F F true (k:=k)] with n ha hn; change duty true n (_+ (1/2:ℂ) • _) = _; rw [map_add, ha,map_smul, hn]; rfl
lemma steady_squares (h:Mut B F) (hf:∀ k, Symm (field p) (F k).val)(he:∀ k,Pure (field p) false (F k).val)(hS:∀ k,Symm (field p) (H k).val): Weightless B F (steadyE B F H):= by
    rw [scales]; intro k; have hs (i) : ∀ᶠ n in atTop, tokM B.district (promote (docket n) F) i=0:= (whorled B F).mp h i;
    filter_upwards [(Finset.eventually_all (Finset.Iic k)).mpr (fun i _=> hs i),(Finset.eventually_all (Finset.Iic k)).mpr (fun i _=>read_dual (B:=B) F H false i)] with n ha hn
    let P:= promote (docket n) F; let T0:= promote (enters n) H; let U:=modulo B.district P T0
    let L' := tokenL B.district.BV true (field p (P:=Site n)); have hl (i:ℕ)(h:i≤k): enters n (steadyE B F H i)=U i:= hn i (Finset.mem_Iic.mpr h)
    simp_rw [promised,hl _ (le_refl k),paired,promised]; change B.district.BV (U k)+(∑ i∈antidiagonal k, L' (P i.1) (enters n (steadyE B F H i.2)))= _; rw [show ∑ i∈antidiagonal k, L' (P i.1) (enters n (steadyE B F H i.2))=pairW L' P U k from Finset.sum_congr rfl (fun i hi=> by rw [hl i.2 (show i.2≤k by obtain he':=Finset.mem_antidiagonal.mp hi; omega)])];
    change modulo B.district P U k=_; unfold U; rw [tokH P T0 k _ _ _,paired,neg_eq_zero];
    · apply Finset.sum_eq_zero; intro i hi; rw [show tokM B.district P i.1=0 from ha _ (Finset.mem_Iic.mpr (by obtain he':=Finset.mem_antidiagonal.mp hi; omega)),map_zero,LinearMap.zero_apply]
    · intro j; change Symm (field p) (sumHome (shown n (F j))).val; simp_rw [total_uses,sum_stack]; exact Symm.sum _ fun i _=> (move_tie (fun x:Site n=>i+x)).sym _ ((move_tie (wrap n)).sym _ (hf j))
    · intro j; change Pure (field p) false (sumHome (shown n (F j))).val; simp_rw [total_uses,sum_stack]; exact Pure.sum _ fun i _=> (move_tie (fun x:Site n=>i+x)).pure _ ((move_tie (wrap n)).pure _ (he j))
    intro i; exact (move_tie (wrap n)).sym _ (hS i)
end YM.MS.Book
