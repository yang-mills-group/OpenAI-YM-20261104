import YM.Integration.FVA1Physical.Wilson.CopiedBank
import YM.Integration.FVA1Physical.Wilson.LocalExterior

/-! A physical coordinate copy needing only the fields in one rooted, enlarged
collar. All the original fields outside the collar remain arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open MSbar MSbar.Lis MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery Comparison.RG02 Push Push.Uniform
open scoped Classical Topology
variable {G : Gauge} {f : Side}

def cutField (H : Support f) (U : Config G f) : Config G f := fun e=>if e.1∈H then U e else 1

theorem cutField_cont (H : Support f) : Continuous (cutField (G:=G) H) := by
  apply continuous_pi
  intro e
  by_cases h : e.1∈H
  · simpa only [cutField,if_pos h] using (continuous_apply (A:=fun _:Edge (Site f)=>G.El) e)
  simpa only [cutField,if_neg h] using (continuous_const : Continuous (fun _:Config G f=>(1:G.El)))

theorem cut_agrees (H : Support f) (U : Config G f) : Agrees H U (cutField H U) := by
  intro e he _
  exact (if_pos he).symm

theorem cut_healthy (t : ℝ) (P : Support f) (U : Config G f) (h : Healthy t P U) :
    Healthy t P (cutField (inspected P) U) := by
  have eq := flags_agree t U (cutField (inspected P) U) P (cut_agrees _ U)
  unfold Healthy at h ⊢
  rw [Finset.disjoint_iff_inter_eq_empty] at h ⊢
  exact eq.symm.trans h

def edgeColors (e : Edge (Site f)) : Finset (Primary f G) := univ.image (fun a : G.ColorIndex=>primary e a)

theorem mem_edgeColors (e : Edge (Site f)) (i : Primary f G) : i∈edgeColors e ↔ rope i=e := by
  constructor
  · rintro h
    obtain ⟨a,_,rfl⟩ := mem_image.mp h
    exact curb e a
  intro h
  exact mem_image.mpr ⟨i.2,mem_univ _,h ▸ curr i⟩

theorem card_edgeColors (e : Edge (Site f)) : (edgeColors (G:=G) e).card=Fintype.card G.ColorIndex := by
  rw [edgeColors,Finset.card_image_of_injective _ (fun _ _ h=>congrArg Prod.snd h),card_univ]

theorem palace_freeze_edge (g : ℝ) (z : Positions (Primary f G)) (e : Edge (Site f)) :
    palace (g • freeze (edgeColors e) z) = update (palace (g • z)) e 1 := by
  let I := edgeColors (G:=G) e
  have fld (q : Edge (Site f)) : panel G f (freeze I z) q = if q=e then 0 else panel G f z q := by
    ext a
    have id : (panel G f (freeze I z) q) a = freeze I z (primary q a) := rfl
    rw [id,freeze]
    by_cases h : q=e
    · rw [if_pos ((mem_edgeColors e _).mpr ((curb q a).trans h)),if_pos h]
      rfl
    rw [if_neg (fun hh=>h ((curb q a).symm.trans ((mem_edgeColors e _).mp hh))),if_neg h]
    rfl
  funext q
  by_cases h : q=e
  · subst q
    rw [update_self,palace,map_smul]
    change G.lieExp (g • panel G f (freeze I z) e)*1=1
    rw [fld,if_pos rfl,smul_zero,G.mat_lieExp_zero,mul_one]
  rw [update_of_ne h,palace,palace,map_smul,map_smul]
  change G.lieExp (g • panel G f (freeze I z) q)*1=G.lieExp (g • panel G f z q)*1
  rw [fld,if_neg h]

theorem cut_update (H : Support f) (U : Config G f) (e : Edge (Site f)) :
    cutField H (update U e 1) = update (cutField H U) e 1 := by
  ext q
  by_cases he : q=e
  · subst q; simp [cutField]
  simp only [cutField, update_of_ne he]

/-- Geometry is built from the actual links and their final flags. The caller
supplies only the local healthy test before and after the one-link change. -/
theorem place_one_bond (t : ℝ) (e : Edge (Site f)) (U : Config G f) (M : ℕ)
    (hu : Healthy t (halo (2*M) {e.1}) U) (hv : Healthy t (halo (2*M) {e.1}) (update U e 1)) :
    let H := inspected (halo (2*M) {e.1})
    let V := update U e 1
    let U' := cutField H U
    let V' := cutField H V
    Heath.Place {e.1} M U U' V V' t ∧ Heath.Place {e.1} M U' U' V' V' t := by
  intro H V U' V'
  let P := halo (2*M) {e.1}
  have base (A : Config G f) : Heath.Spine {e.1} A (update A e 1) :=
    fun X dis => Heath.stitch e A 1 X (by simpa only [Finset.disjoint_singleton_right] using dis)
  have u : Heath.Spine {e.1} U V := base _
  have v : Heath.Spine {e.1} U' V' := by
    change Heath.Spine {e.1} U' (cutField H (update U e 1))
    rw [cut_update];exact base U'
  have area : P ⊆ H := fun j hj=>Finset.mem_union_left _ hj
  have au : Agrees P U U' := agrees_mono (cut_agrees H U) (coe_subset.mpr area)
  have av : Agrees P V V' := agrees_mono (cut_agrees H V) (coe_subset.mpr area)
  exact ⟨⟨u,v,au,av,hu,hv⟩,⟨v,v,fun _ _ _=>rfl,fun _ _ _=>rfl,cut_healthy t P U hu,cut_healthy t P V hv⟩⟩

end YM.Integration.FVA1Physical.Wilson
