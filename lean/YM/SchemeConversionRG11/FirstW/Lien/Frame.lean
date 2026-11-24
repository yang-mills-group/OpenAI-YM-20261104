import YM.SchemeConversionRG11.FirstW.Lien.Vault
/-! Actual allowed field CT space. Use frame-space to choose lifts equivariant. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial Position SchemeConversionRG11 SchemeConversionRG11.Horizon
open scoped BigOperators Classical
variable {G : Gauge} (F : Labels.Frames G)
-- `Hex` are fields with quadr polynomial labels. Already extended to unusual parent slots.
def Hex : Submodule ℂ (E F 6) := (Reel G).comap (Full.sections 6 F)
def sendP (q : Paper G): E F 6 := RawLabels.enroll F 6 (⟨q.val,(vaulted.mp q.property.1).1,q.property.2⟩)
lemma send_ref (q : Paper G): Full.sections 6 F (sendP F q)=q.val:=by rw [Full.sections, sendP,LinearMap.comp_apply,embed_round]; exact (vaulted.mp q.property.1).2.2
variable {F}
def sink (v : E F 6) := v∈ lower F 5 6
lemma sink_zero (a : ℕ) (h:a<6) : lower F a 6 ≤ lower F 5 6 := by
 rw [←incl_range F h.le, ←incl_range F (by decide: (5:ℕ)≤6)]; rintro v ⟨p,rfl⟩; have hp : a≤5:= by omega
 exact ⟨_,incl_repeat F hp (by decide) p⟩
lemma sink_bar {p : E F 6} (h:sink p): sink (bar F 6 p) := by
 unfold sink at *; rw [←incl_range F (by decide: (5:ℕ)≤6)] at *; obtain ⟨x,rfl⟩:=h; exact ⟨_,incl_bar F _ x⟩
variable (F)
abbrev tripS (s:Signed): Module.End ℂ (E F 6):= (rideO F s.ortho 6).toLinearMap
lemma trip_p (u v:Signed)(x:E F 6): tripS F u (tripS F v x)=tripS F (u*v) x := by
 apply writes_inj F 6; change writes F 6 (ride _ _ _ (ride _ _ _ x)) = writes F 6 (ride F _ _ x); rw [ride_at,ride_at,ride_at,show (u*v).ortho=u.ortho*v.ortho from Signed.inclusionO.map_mul ..,← pull_mul]
lemma trip_b (s:Signed) (p:E F 6): bar F 6 (tripS F s p)= tripS F s (bar F 6 p) := by
 apply (Function.Injective.comp Subtype.val_injective (show Function.Injective (physicalLabel F 6) from fun x y h=>by rw [← RawLabels.physical_round F x,h, RawLabels.physical_round])) -- simpler
 simp only [comp_apply,bar, tripS, LinearEquiv.coe_coe, RawLabels.physical_real, RawLabels.physical_ortho,Labels.real_turn]
lemma trip_i (p:E F 6): tripS F 1 p=p:=by
 apply writes_inj; change writes _ _ (ride _ _ _ _) = _; rw [ride_at,show (1:Signed).ortho=1 from Signed.inclusionO.map_one,pull_one]
lemma trip_s (s:Signed)(p:E F 6) (h:sink p): sink (tripS F s p):=by
 unfold sink at *; rw [←incl_range F (by decide : (5:ℕ)≤6)] at *; obtain ⟨x,rfl⟩:=h; exact ⟨_,incl_rotate F _ s x⟩
lemma send_H (u: E F 6): Labels.changed (rebase G) (Full.sections 6 F u)=Full.sections 6 F u := by
 have he:=RawLabels.embed_round F (RawLabels.physicalLabel F 6 u); rw [RawLabels.physical_round] at he; exact congrArg Subtype.val he.symm
lemma well_H (u:E F 6): Full.sections 6 F u ∈ Labels.limited G 6:= (physicalLabel F 6 u).property.1
lemma trip_H (s:Signed){u:E F 6}(h:u∈ Hex F): tripS F s u∈ Hex F := by
 refine vaulted.mpr ⟨well_H _ _,?_,send_H _ _⟩
 rw [show Full.sections 6 F (tripS F s u)=Labels.rotated s.ortho (Full.sections 6 F u) from congrArg Subtype.val (RawLabels.physical_ortho F s.ortho u)]
 exact change_weight _ (show _∈ census G 2 from (vaulted.mp (show _∈ Reel G from h)).2.1) _
lemma trip_B (u:E F 6)(h:u∈Hex F) : bar F 6 u∈ Hex F:= by
 have he: Full.sections 6 F (bar F 6 u)= Labels.conjPol (Full.sections 6 F u):= congrArg Subtype.val (RawLabels.physical_real ..)
 refine vaulted.mpr ⟨well_H _ _,?_,send_H _ _⟩
 intro t ht; apply (vaulted.mp (show _∈ Reel G from h)).2.1
 intro ef; apply ht; rw [he,Labels.conjPol,coeff_map,ef,map_zero]
-- reads on cover coordinates of transformed field
lemma trip_test (s:Signed)(p:E F 6)(x y : Field4 G) : chord x y (Full.sections _ F (tripS F s p))=chord (Bare.wideLink G s x) (Bare.wideLink G s y) (Full.sections _ F p) := by
 have he (x:Field4 G): sun x (Full.sections _ _ (tripS F s p))=sun (Bare.wideLink G s x) (Full.sections 6 F p) := by
    simp only [sun,←seen,tripS,LinearEquiv.coe_coe,cirrus,swayL,lit_any]; rw [show (fun i => Labels.Taylor.turn s⁻¹.ortho (stageW G x i))= stageW G (Bare.wideLink G s x) from funext fun i=>by simp only [stageW,LinearMap.pi_apply,linear_symm,affine,Signed.act_zero,zero_add]]
 rw [chord_at,chord_at,he,he,he,map_add]
lemma trip_star (p:E F 6)(x y:Field4 G): chord x y (Full.sections _ F (bar F 6 p))=star (chord x y (Full.sections _ F p)):=by
 rw [show Full.sections 6 F (bar F 6 p) = Labels.conjPol (Full.sections 6 F p) from congrArg Subtype.val (RawLabels.physical_real ..),chord_at,chord_at]; simp [sun,Labels.conj_value]
end YM.RG11.FirstW
