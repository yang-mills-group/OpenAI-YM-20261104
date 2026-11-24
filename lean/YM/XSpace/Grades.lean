import YangMills.WilsonProof.GraphOperands
import YM.XSpace.Forecast
import YangMills.WilsonProof.NativeSupport.YM.XSpace.OnShell
import YM.Next.MAXWELL.Shelves
/-!
# Infinite growing frame: splitting by engineering grades.
All policies set on exactly the on-shell filtration. Reparameterizing the bases
of the relative grade spaces not needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d j n m:ℕ}
def en (h:n≤d): (On.Grade G n)→ₗ[ℂ] Sec G d:= Submodule.inclusion (le_trans (show On.Grade G n≤shellSector G n from inf_le_left) (chain h))
abbrev engineering (n:ℕ) (G:Gauge):=MvPolynomial.weightedHomogeneousComponent (R:=ℂ) (scaleW (G:=G)) n
private lemma cp (p:Sec G d) (n:ℕ): engineering n G p.val∈On.Grade G n:=by
  let Y:=engineering n G p.val; have h1 : MvPolynomial.IsWeightedHomogeneous scaleW Y n:= MvPolynomial.weightedHomogeneousComponent_mem ..
  have hd : Y∈ shellSector G d:= colors_grade (fun i=>i+2) n p.property
  refine ⟨sector.mpr ⟨?_,(sector.mp hd).2⟩,h1⟩; rw [lowerCap, MvPolynomial.mem_restrictSupport_iff]; exact fun _ hv=> (h1 (MvPolynomial.mem_support_iff.mp hv)).le

def part (d n: ℕ): Sec G d →ₗ[ℂ] On.Grade G n:= LinearMap.codRestrict _ (engineering n G ∘ₗ coeS d) (fun p=> cp p n)
lemma val_part (p:Sec G d) (n:ℕ): (part d n p).val=engineering n G p.val:=rfl
lemma part_same (p:On.Grade G n) (h:n≤d) : part d n (en h p)=p:=Subtype.ext (show engineering n G p.val=p.val from (show MvPolynomial.IsWeightedHomogeneous .. from p.property.2).weightedHomogeneousComponent_same)
lemma part_other (p:On.Grade G n) (hk:m≠n) (h:n≤d) : part d m (en h p)=0:=Subtype.ext (show engineering m G p.val=0 from (show MvPolynomial.IsWeightedHomogeneous .. from p.property.2).weightedHomogeneousComponent_ne m hk)
lemma part_up (h:j≤d) (p:Sec G j) (n:ℕ) : part d n (up h p)=part j n p :=rfl
lemma en_up {h:j≤d} {H:n≤j} (p:On.Grade G n): up h (en H p)=en (le_trans H h) p:=rfl
lemma part_zero (h:d<n) (p:Sec G d): part d n p=0:=by
  have hk: p.val∈lowerCap G d:=(sector.mp p.property).1; rw [lowerCap,MvPolynomial.mem_restrictSupport_iff] at hk
  apply Subtype.ext; ext i; simp only [val_part,engineering,MvPolynomial.coeff_weightedHomogeneousComponent,Submodule.coe_zero,MvPolynomial.coeff_zero]; split_ifs with he
  · by_contra hp; apply Nat.not_le_of_gt h; exact he ▸ (show Finsupp.weight scaleW i≤d from hk (MvPolynomial.mem_support_iff.mpr hp))
  rfl
lemma enfits (p:Sec G d) : ∑ i: Fin (d+1), en (show i.val≤d from Nat.lt_add_one_iff.mp i.isLt) (part d i p)= p := by
  apply Subtype.ext; ext k; simp only [Submodule.coe_sum,MvPolynomial.coeff_sum]
  change ∑ i: Fin (d+1), (engineering i G p.val).coeff k = p.val.coeff k
  have hu : p.val∈lowerCap G d:=(sector.mp p.property).1; rw [lowerCap,MvPolynomial.mem_restrictSupport_iff] at hu
  simp only [engineering,MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases he : p.val.coeff k=0
  · simp [he]
  let z: Fin (d+1):=⟨Finsupp.weight scaleW k, Nat.lt_add_one_iff.mpr (hu (MvPolynomial.mem_support_iff.mpr he))⟩
  rw [Finset.sum_eq_single z, if_pos (show _ = _ from rfl)]
  · exact fun a _ ha=> if_neg fun hf=> ha (Fin.ext hf.symm)
  simp
lemma part_ori (s:Ortho) (p:Sec G d) (n:ℕ): (part d n (ori s d p)).val=reflectPol s (part d n p).val:= gloss_mirror (fun i=>i+2) n s p.val
lemma part_reel (p:Sec G d) (n:ℕ): (part d n (reel d p)).val=realForm (part d n p).val:= real_gloss (fun i=>i+2) n p.val

def prev (d:ℕ): Sec G (d+1)→ₗ[ℂ] Sec G d:= ∑ i: Fin (d+1),en (show i.val≤d from Nat.lt_add_one_iff.mp i.isLt) ∘ₗ part (d+1) i
abbrev step (d:ℕ): Sec G d→ₗ[ℂ] Sec G (d+1):=up (Nat.le_succ _)
lemma prev_step (p: Sec G d): prev d (step d p)=p:=by unfold prev; simp only [LinearMap.sum_apply,LinearMap.comp_apply]; exact enfits p
lemma ori_step (s:Ortho) (p:Sec G d): step d (ori s d p)=ori s (d+1) (step d p):=rfl
lemma reel_step (p:Sec G d): step d (reel d p)=reel (d+1) (step d p):=rfl
lemma prev_ori (s:Ortho) (p:Sec G (d+1)): ori s d (prev d p)=prev d (ori s (d+1) p):=by
  unfold prev; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i _=> Subtype.ext (part_ori s p i).symm
lemma prev_reel (p:Sec G (d+1)): reel d (prev d p)=prev d (reel (d+1) p):=by
  unfold prev; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i _=> Subtype.ext (part_reel p i).symm
end YM.XSpace.Normalize
