import YM.FullVolume.Lit
import YM.Integration.WilsonMatrixOriginalDeckColumns

/-! The true finite Haar-equation quotient has the dimension of the booked
independent Maxwell basis, including its original unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPhysicalRank
open Function Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Next.Rank Next.Rank.Market Push.RelayDifference
open Next.Extract MergeProof Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open scoped Classical Topology
variable {G:Gauge} (C:Family G)
theorem original (B:Deck G) (d:ℕ) (V:∀d,Source.SectionData (C.labels.level d)) (R:Push.Mark.Weave G)
    {P:∀ d,Cutoffs→(C.label d≃ₗ[ℂ]C.label d)} (a:Presentation C) {ζ:ℕ→ℕ→ℝ}
    (hf:Hearthside C V R P a ζ) (i:Cutoffs) :
    Module.finrank ℂ (LinearMap.range (a.step d i).toLinearMap)=Fintype.card (Glyph B d):=by
   let v:= bindP C R d i.1 i.2 (P d i)
   let F:= C.labels.level d
   let T:= Maxwell.freeTable C.labels; let U:= Maxwell.equationIdeal G d
   have hg : T.null d=U.map F.coords.toLinearMap:=by
      ext x; obtain ⟨j,rfl⟩:= F.coords.surjective x
      change F.coords j∈ T.null d ↔ _
      have hh : F.coords j∈T.null d ↔ j∈U:= by
        have H := Maxwell.projectionExact C.labels (c:=F.coords j)
        rw [Extra.FD.no_residual] at H
        refine H.symm.trans ?_; simp only [Submodule.mem_bot]; constructor
        · intro h; apply LinearMap.mem_ker.mpr
          have hh : Maxwell.observable G d ((C.labels.level d).coords.symm (F.coords j))=0 := congr_arg Subtype.val h
          rw [F.coords.symm_apply_apply] at hh; exact hh
        intro h; apply Subtype.ext
        change Maxwell.observable G d ((C.labels.level d).coords.symm (F.coords j))=0; rw [F.coords.symm_apply_apply]; exact h
      rw [hh]; exact ⟨fun hi=> ⟨j,hi,rfl⟩,fun ⟨k,h,hj⟩=> F.coords.injective (show F.coords k=F.coords j from hj) ▸ h⟩
   have he := LinearEquiv.finrank_eq (v.submoduleMap U)
   have hz := LinearEquiv.finrank_eq (F.coords.submoduleMap U)
   have ha : Module.finrank ℂ (T.Field d)+Module.finrank ℂ (T.null d) = Module.finrank ℂ (C.label d):= (T.null d).finrank_quotient_add_finrank
   have hb : Module.finrank ℂ (LinearMap.ker (a.step d i).toLinearMap) = Module.finrank ℂ U:= (congrArg (fun W : Submodule ℂ (C.label d) => Module.finrank ℂ W) (hf.foundation.step d i.1 i.2).ker).trans he.symm
   have hz' : Module.finrank ℂ (T.null d)=Module.finrank ℂ U:=
      (congrArg (fun W : Submodule ℂ (C.label d)=> Module.finrank ℂ W) hg).trans hz.symm
   have hK : Module.finrank ℂ (T.Field d)=Fintype.card (Glyph B d):=
     Module.finrank_eq_card_basis (WilsonMatrixOriginalDeckColumns.basis C B d)
   have hx:= LinearMap.finrank_range_add_finrank_ker (a.step d i).toLinearMap
   rw [hz',hK] at ha; rw [hb] at hx; exact Nat.add_right_cancel (hx.trans ha.symm)
end YM.Integration.WilsonThermometerWeakPhysicalRank
end
