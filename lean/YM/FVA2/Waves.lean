import YM.FVA2.Substitute
import YM.MS.Swirl.Resolute

/-!
# Coordinates for the `PhysicalSum` vertices

Ordinary phases on links (not midpoint). The weights stored in `Bulk`, `frameL`
undo the half-shifts in the Wilson core. For any cylinder, exactly a linear
substitution `ξ`, including arbitrary wraps. Polys here still in undilated
alphabet -- strip/dress issues later.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2
open Matrix Function Set Filter Lattice MS MS.Cylinder MS.Koszul MS.Native MS.Native.Wilsonian MS.Cylinder.Lab
open MS.Plane MS.Landau MS.Momentum MS.Book MS.Tone MS.City MS.Orbit MS.Orbit.Cog
open MS.Fleet MS.Swirl MS.Swirl.Near
open FVA2.Substitute
open scoped Classical
namespace Inversion
variable {G:Gauge} {n:Side}
local notation "I"=> FixedMode G n
open Bloch (cell)

lemma δW (n:Side) : brightness n=(n.val:ℂ)^4:= by simp [scaleZ,brightness,νt]
lemma scaled (n:Side) : scaleZ n * (n.val:ℂ)^4=1:= by rw [← δW]; exact lightW n
lemma useful (n:Side) : scaleZ n ≠0:= left_ne_zero_of_mul (by rw [scaled n]; exact one_ne_zero : scaleZ n * (n.val:ℂ)^4≠0)

def Fourier (G:Gauge)(n:Side) : Matrix (FixedMode G n) (FixedMode G n) ℂ:= Matrix.of fun i j=> if j.1=i.1 then cell i.2 j.2 else 0
def upWave (G:Gauge)(n:Side) : Matrix (FixedMode G n) (FixedMode G n) ℂ:= Matrix.of fun i j=> if j.1=i.1 then scaleZ n * cell i.2 (-j.2) else 0
local notation "ϕ"=> Fourier G n
local notation "w"=> upWave G n
lemma invert_F : ϕ*w=1 := by
  ext ⟨a,i⟩ ⟨b,j⟩; rw [mul_apply, Fintype.sum_prod_type,Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · by_cases h:a=b
    · subst b; simp only [Fourier,upWave, Matrix.of_apply,↓reduceIte,Matrix.one_apply,Prod.mk.injEq,true_and]
      simp_rw [Bloch.cell_inverse, show ∀ k:Site n,cell k j=cell j k from fun k=>Bloch.cell_duality k j, mul_left_comm _ (scaleZ n), ← Finset.mul_sum, Bloch.orthogonal]; split; exact scaled n; simp
    simp [Fourier,upWave,h,Ne.symm h]
  intro c hc hh; simp [Fourier,hh]
lemma invert_F' : w*ϕ=1:= mul_eq_one_comm.mp invert_F
lemma kind_F : TieField ϕ (σbranch (n:=n)) σbranch := by rintro ⟨a,i⟩ ⟨b,j⟩ h; by_cases hx:a=b; subst b; rfl; exact (h (by simp [Fourier,Ne.symm hx])).elim

lemma emit_phase (F: Dot G Cover) : ξ[ϕ] (enters n F)=rentS G n (sleeve lace (Tone.run F)):= by
  rw [show enters n F=(Ferry (post (wrap n)) F).val from rfl,asShade,study]
  have ha (i:I)(j: LightMode G Cover) : ϕᵀ i (post (wrap n) j) = lace (addr i)*paywave (addr i) j := by
    rcases i with ⟨a,i⟩; rcases j with ⟨b,j⟩
    by_cases hb:a=b
    · subst b; change (if a=a then cell (wrap n j) i else 0) =_
      rw [if_pos rfl]; change Φa j i= lace (addr (a,i))*paywave (a,_) (a,j); rw [pw,rightadd,φ_c]; unfold be; rw [Tone.rights];
      rw [mul_left_comm,show lace (addr ((a,i) : FixedMode G n))*bill _ (offset a.1) = 1 from (mul_comm ..).trans (lace_ (addr ((a,i) : FixedMode G n))),mul_one]
    change (if a=b then cell (wrap n j) i else 0)=_
    rw [if_neg hb,show paywave _ _ =0 from Classical.byContradiction (fun he=>hb (in_light _ _ he)),mul_zero]
  funext l; induction l generalizing F with
  | nil=> simp [rentS,Tone.run, Orbit.stage,hook]
  | cons i l IH=>
    obtain ⟨s,hs⟩ := fromCyl F
    rw [deriv_lum (fun i j=> ϕᵀ i (post (wrap n) j)) i F hs ]; change _= sleeve _ _ (_::stage l)
    simp_rw [IH,ha]; unfold Tone.run; simp only [rentS,LinearMap.coe_mk,AddHom.coe_mk,Function.comp_apply,sleeve_here,deriv_lum paywave _ _ hs,hook,List.map_cons,List.prod_cons,Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=>by ring
lemma emit_here (F:Dot G Cover)(x: Cover): ξ[ϕ] (enters n (Lab.Shift x F))= Orbit.anchor G n x (sleeve lace (Tone.run F)):= by
    rw [emit_phase]; funext l; rw [chase_now]; change sleeve _ _ _=_*sleeve lace _ _
    rw [sleeve_here, sleeve_here,movement,φ_s]; unfold be; rw [Tone.rights]; ring

lemma labels_marks (F: Dot G Cover) (x y:Cover) : Near.Mark_T G n x y F=
      ξ[ϕ] (enters n (Lab.Shift (x+y) F)):= by
    rw [emit_here]; funext l; unfold Mark_T;
    change anchor G n x (frameL y (Tone.run F)) l=_; rw [chase_now,chase_now,Orbit.point,Orbit.point,f_l, lodg,φ_s,φ_s]; simp only [be,emb_add,Tone.payadd]; ring

lemma labels_bulk (F:Dot G Cover) : Bulk G n (sleeve lace (Tone.run F))=
      ξ[ϕ] (docket n F):= by
    rw [show docket n F = ∑ i:Site n,enters n (Lab.Shift (lift i) F) from ?_,map_sum]
    · simp_rw [emit_here]; funext l; simp_rw [bulkZ, Finset.sum_apply, chase_now, ← Finset.sum_mul]
      unfold Φa; simp_rw [wrap_lift]
      split_ifs with hx
      · simp [hx,δW n]
      simp_rw [show ∀ i:Site n,cell i (net l)=cell (net l) i from fun i=> Bloch.cell_duality ..,Bloch.sum_cell hx,zero_mul]
    unfold docket enters; simp_rw [LinearMap.comp_apply, shown, trans_shift,wrap_lift, total_uses,map_sum]

lemma volume_F (F:Dot G Cover) (b:Bool): SendB G n b F=ξ[ϕ] (pay b • docket n F) := by
  rw [map_smul,SendB,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.comp_apply,labels_bulk]

end Inversion
end YM.FVA2
