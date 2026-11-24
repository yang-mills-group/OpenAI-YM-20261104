import YM.MS.Local.Physical
import YangMills.WilsonProof.NativeSupport.YM.MS.Color.Image
/-!
# Local continuum physical lifts

Unit from zero. Real local free class represented by invariant symmetric products of
curvature (no pure ghost). Need quotient by linear equations,Bianchi and equation
completed exacts; present as any canonical choice of splitting EXACT in span. Compare
for construction; lifting to $D$ continuum later. Use real-linear spaces for marking.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.Physical
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open Color Landau Detect Local BV Woven
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {F : Law G} {r:ℕ} {h q:ℤ}
lemma rd (w : List (Lane4 G)): fieldDim mslug w= fieldDim wfield w-fieldDim ghostNo w:= by
    induction w with
    | nil=> rfl
    | cons i w ih=> simp only [field_cons,ih]; unfold mslug; omega
-- for chart nets arbitrary derivative parameter E
lemma smudge : Form F mslug h false ↔ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E], ∀ w : Wire (Branch G Axis) E FourP,
    Plane.Shape (fieldVal F w) (h- fieldDim wfield w+fieldDim ghostNo w) := by
   have he (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w:Wire (Branch G Axis) E FourP): h-fieldDim mslug w=h-fieldDim wfield w+fieldDim ghostNo w:= by rw [← sail_dim w (0:E),rd,sail_dim,sail_dim]; omega
   exact ⟨fun h E _ _ w=> he E w ▸ h E w (fun v=> Bool.noConfusion v),fun h E _ _ w _=> he E w ▸ h E w⟩
lemma shadow (F:Law G): (∀ w, F (invertMom w)=star (F w)) ↔ overC F=F:= by
    refine ⟨fun h=>?_ ,fun h w=>?_⟩
    · ext w; exact (congr_arg _ (h w)).trans (star_star _)
    exact star_injective ((congr_fun h w).trans (star_star _).symm)
lemma room (F:Law G) (q:ℤ): Solid false F q ↔ Bright F ∧ (∀ w:Legs (Lane4 G), fieldDim ghostNo w≠q → F w=0):= by
    constructor
    · intro H; refine ⟨⟨fun l i j r =>H.symm _ _ _ _ (fun v=> Bool.noConfusion v),?_,(shadow F).mp (fun w=> H.real' _ (fun v=> Bool.noConfusion v))⟩, fun w=> H.ghost w (fun v=>Bool.noConfusion v)⟩
      intro x; ext w; exact H.color w (fun v=> Bool.noConfusion v) _
    rintro ⟨h,h'⟩; exact ⟨fun _ _ _ _ _=>h.weight _ _ _ _,fun w _=> h' w,fun w _ x=> congr_fun (h.color x) w,fun w _=>(shadow F).mpr h.shadow w⟩

lemma shift_grade (hp:∀ w:Legs (Lane4 G), fieldDim ghostNo w≠q→ F w=0): Form F wfield h false ↔ Form F mslug (h-q) false:= by
   rw [smudge]; have hz (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w:Wire (Branch G Axis) E FourP) (h:fieldDim ghostNo w≠q): fieldVal F w=0:= funext fun x=> hp _ (sail_dim w x ▸ h)
   constructor
   · intro H E _ _ w; by_cases he:fieldDim ghostNo w=q; · rw [he,show h-q-fieldDim wfield w+q=h-fieldDim wfield w by omega]; exact H E w (fun v=> Bool.noConfusion v)
     rw [hz E w he]; exact form_zero _
   intro H E _ _ w _; by_cases he:fieldDim ghostNo w=q; · obtain hH:= H E w; rw [he,show h-q-fieldDim wfield w+q=h-fieldDim wfield w by omega] at hH; exact hH
   rw [hz E w he]; exact form_zero _

lemma smooth_branch : Solid false F q ∧ Form F wfield h false ∧ Ranked false r F ↔ Bright F ∧ F∈ Bed G (h-q) q r:= by
    rw [room]; refine ⟨fun ⟨⟨he,hh⟩,h,h'⟩=>⟨he,tileCub.mpr ⟨(shift_grade hh).mp h,hh,fun w=>h' w (fun v=>Bool.noConfusion v)⟩⟩,?_⟩
    rintro ⟨hp,H⟩; let v:=tileCub.mp H; exact ⟨⟨hp,v.tag⟩,(shift_grade v.tag).mpr v.shape,fun w _=> v.rank w⟩
section spaces
open Color
variable {F H : Law G}

variable (G)

variable (h r q)

-- `Allowed h` are A-sector even polynomials with horizon h (effective grade h at ghost 0).
-- physical-null pre-relations on A-sector: exactly linear $Q$ exacts that end in sector.
end spaces
lemma lease_one : F∈ Lease G h r q ↔ Solid false F q ∧ Form F wfield h false ∧ Ranked false r F:= (and_comm.trans smooth_branch.symm) -- goal unfolds?
lemma allowed_pure (hF:F∈Allowed G h r): natQ F=0:= carry_pure ((byGuide _).mp hF).1
lemma exacts (hp : F∈Lease G h r 0) (ht:natQ F=0): F∈ Allowed G h r ⊔ (Lease G (h-1) r (-1)).map (kills G):= by
   obtain ⟨hf,hv⟩:=byGuide _ |>.mp hp; obtain ⟨f,hf,Q,hQ,he,hq,hF⟩:= singular (h:=h) (by simpa using hf) ht hv
   rw [hF]; exact add_mem_sup (byGuide _ |>.mpr ⟨hf,he⟩) ⟨Q,byGuide _|>.mpr ⟨by simpa using hQ,hq⟩,rfl⟩

-- finite real basis.
end YM.MS.Local.Physical
