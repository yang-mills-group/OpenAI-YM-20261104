import YM.Integration.WilsonOriginalGalleryTwins

/-! All charged parts of the original numerator agree on every group field, before any averaging. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGalleryTwinsField
open Finset Function Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open Extra.Histories Extra.Trajectories QuadraticLocal.Fusion.Attached Lodestar WilsonOriginalGalleryTwins
open scoped BigOperators Classical
variable {V T I : Type} [DecidableEq V] [Fintype V] [Countable I] {G:Gauge}{n:Side}{P:Rep G n}
  {o:V → Site n}(A:Gallery T I o P (Marks V))(x:T)(w:V → ℝ)(wp:∀i,0<w i){a q k:ℝ}
  (expo:0≤a)(reg:A.E.Paid w P.p.B a q)(forced:A.K.Paid w P.p.B a k)

include wp expo reg in
omit [Countable I] in
private theorem regular (U:Config G n):
    (∑j,soft A x j U)=WilsonPhysicalHistoryGroupedClear.localLog A.E x U:=by
  obtain ⟨_,sum⟩:=(WilsonPhysicalHistoryGroupedLamps.stored A.E w wp {j|¬A.E.clear j} expo reg x).repair wp U
  have charged:=(border A.E.ground sum).tsum_eq
  rwa [tsum_fintype] at charged

include wp expo forced in
omit [Countable I] in
private theorem wharf (b:Box n)(U:Config G n):
    WilsonPhysicalHistoryGroupedHard.grouped P o A.K univ x b U=
    bar P.activities (Marks V) U b+hard A x b U:=by
  ext s
  rw [Poly.part_plus,WilsonPhysicalHistoryGroupedEligibility.coefficient P o A.K w wp _ expo forced]
  unfold hard
  rw [WilsonPhysicalHistoryGroupedEligibility.coefficient P o A.K w wp _ expo forced]
  by_cases h:s=(Marks V).quiet
  · subst s
    rw [if_pos (mem_univ _),if_neg (show (Marks V).quiet∉(univ:Finset (Marks V).Mode).erase (Marks V).quiet by simp),add_zero]
    change _=(Poly.send (Marks V).quiet _).part (Marks V).quiet
    rw [Poly.part_send,if_pos rfl]
    exact tsum_congr fun i=>A.K.quiet x i.val U
  · rw [if_pos (mem_univ _),if_pos (mem_erase.mpr ⟨h,mem_univ s⟩)]
    change _=(Poly.send (Marks V).quiet _).part s+_
    rw [Poly.part_send,if_neg h,zero_add]

include wp expo reg forced in
theorem original (U:Config G n):
    duplicate V (A.density x U)=duplicate V (Poly.pass (clear A x))* entered A x U:=by
  let a₀:=WilsonPhysicalHistoryGroupedClear.localLog A.E x U
  let F:=fun b=>WilsonPhysicalHistoryGroupedHard.grouped P o A.K univ x b U
  have learned:=(regular A x w wp expo reg U)
  have silent:a₀.part (Marks V).quiet=0:=by
    change (WilsonPhysicalHistoryGroupedClear.localLog A.E x U).part _=_
    rw [←learned,Poly.part_sum]
    exact Finset.sum_eq_zero fun b _=>(WilsonPhysicalHistoryGroupedHealthy.fields A.E w wp
      {j|¬A.E.clear j} expo reg (fun _ hi=>hi) x b).sil U
  have hf (s):duplicate V (Accent.field F s)=Accent.field (fun b=>duplicate V (F b)) s:=by
    unfold Accent.field
    rw [map_sum]
    refine Finset.sum_congr rfl fun _ _=>?_
    unfold grid
    split
    · rw [map_prod]
    rw [map_zero]
  have hf₀ (b:Box n):duplicate V (F b)=bar P.activities (Marks (V×Bool)) U b+duplicate V (hard A x b U):=by
    rw [show F b=_ from wharf A x w wp expo forced b U,map_add]
    congr 1
    change duplicate V (Poly.send (Marks V).quiet _) = _
    rw [seal_send,two_quiet]
    rfl
  have h0:Mach (Marks (V×Bool)) (fun _=>0)=0:=by simp [Mach]
  rw [WilsonPhysicalHistoryGroupedGas.density A w wp expo reg forced, map_smul,map_mul,map_mul]
  unfold entered restore
  simp only [Pi.zero_apply,h0,zero_add,add_zero,Function.comp_apply]
  change ∑j,soft A x j U=a₀ at learned
  rw [mul_smul_comm,seal_pass _ silent,←learned,map_sum,hf,funext hf₀]
  simp only [mul_assoc,clear]

include wp expo reg forced in
theorem part (U:Config G n)(s:(Marks V).Mode):
    (A.density x U).part s=(duplicate V (Poly.pass (clear A x))*entered A x U).part (two s):=by
  rw [←original A x w wp expo reg forced U,seal_part]

end YM.Integration.WilsonOriginalGalleryTwinsField
end
