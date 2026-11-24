import YM.MS.Menus.Quantify
import YM.MS.High.Standard
/-!
# Leading cubic kinetic tensor, defined by order-one source symbol

Determine by Class. The comparison to continuum needs one physical test of ghost Lie parameter.
 Contact terms ignored only later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost Detect Detect.Mark Wire
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge} {w:List (Lane4 G)} (p:Team) (x:ℝ)
-- universal styles agree rank 3 at order1. Reuse ℂ series lemmas.
lemma sub_one (F:T (Dot G Cover)): substitute (shift p x) F 1=F 1 := by
   rw [rules,Finset.sum_eq_single 1]
   · simp [Program.cut,ann]
   · intro k hk hv; rw [show k=0 from (by simp at hk; omega)]; simp [Program.cut]
   simp
lemma plan_1 (F:T (Dot G Cover)): wobble G p x F 1= F 1+ train (Y p x) 1 (F 0):= by
    rw [wobble,LinearMap.comp_apply,rolls]; simp only [Finset.Nat.sum_antidiagonal_succ,Finset.Nat.antidiagonal_zero,Finset.sum_singleton, sub_one p x F, Program.pay0]; rw [show train _ 0 (F 1)=_ from frame_clock x p _]
abbrev Top (G:Gauge):= Book.mask 3 (run (core G 1))
lemma maskOff {F:Law G} {u v:ℤ}(hp:u<v)(h:Limit F u): Book.mask v F=0:= by ext l; by_cases he:(l.length:ℤ)=v; exact (enough l he).trans (h l (by omega)); exact strange _ he
lemma Top_P : Book.mask 3 (run (style G p x 1))=Top G:= by unfold style; rw [plan_1 p x (core G),map_add,map_add,maskOff (u:=2) (by decide) (oneRank (merited (Y p x) (core G 0) (participates G 0))), add_zero] -- maybe lint
lemma Top_closed (h:G.Simple) (w:List (Lane4 G))(hw:net w=0) : (send wave).raise (Top G) w=0:= by
    let p:Team:= fun _=>⟨0,0,0⟩
    let F:= style G p 0 1; let A:= promote run (style G p 0)
    have ht := plane_core p 0 h w hw (k:=1) (by omega); change (send wave).raise (run F) w+ _+ (1/2:ℂ)*(∑ j∈Domain.paths 1 1,tree Landau.parity (Kzone G) (A (1-j)) (A j) w)= _ at ht
    rw [← Top_P p 0, ← mask_raises]; by_cases hx : (w.length:ℤ)=3; swap; · exact strange _ hx
    rw [enough _ hx]; unfold Domain.paths at ht; rw [show cycle (Kzone G) μzone (A 1) w= run ((Spectrum G).Lap F) w from congr_fun (lapC F ((core_circle G p).actual .. |>.symm)).symm w] at ht
    have hf : Limit (run ((Spectrum G).Lap F)) 1:= oneRank (lapLimit (style_limit p 0 G 1)); simpa [hf w (by omega)] using ht

-- class = skin. Need smooth local. promote later versions.
lemma all_smooth {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] (F:Dot G Cover)(w:Wire (Branch G Axis) E FourP): ContDiff ℝ ∞ (fieldVal (run F) w):= by
    induction w generalizing F with
    | nil=> exact contDiff_const
    | cons i w ih=>
       obtain ⟨s,hs⟩:=obliges F; unfold fieldVal; simp only [sail_cons,grows F hs]; refine ContDiff.sum fun j _=>ContDiff.mul ?_ (ih _); unfold bill pairing; refine ContDiff.cexp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun x:E=> ∑ j':Axis, i.2 x j'*bornv (i.1,j) j') by fun_prop))) -- reducible `Contour`
abbrev LE (G:Gauge)(i:ℤ):= skin wfield i (Top G)
lemma Top_model : Top G=run (Book.model 3 (core G 1)):= (Tone.grade ..).symm
lemma Top_off (w:List (Lane4 G))(h:w.length≠3): Top G w=0:= strange _ (by omega)
lemma Top_field_off (w:List (Lane4 G))(h:w.length≠ 3): fieldVal (Top G) (ray w)=0:= funext fun _=> Top_off _ (by simp [h])
lemma LE_off (w:List (Lane4 G))(h:w.length≠ 3)(i:ℤ): LE G i w=0:= by
   unfold LE skin; split
   · rw [torch_at]; change reading _ (fieldVal (Top G) (ray w))=0; rw [Top_field_off w h]; simp [reading]
   rfl
lemma Top_lead (G:Gauge)(v:ℤ)(h:∀ w:List (Lane4 G), w.length=3→ Course true w→∀ j:ℕ,fieldDim wfield w+j<v→ torch j (Top G) w=0): Lifting.Face wfield (Top G) (LE G v) v true:= by
    intro w hw; by_cases he:w.length=3; swap; · rw [Top_field_off w he,LE_off w he]; exact Rest.zero _
    refine ⟨?_,fun hv=> by unfold LE skin; exact if_neg (by omega), fun j hi=> ?_⟩; · rw [Top_model]; exact all_smooth ..
    change torch j _ w= _; split
    next hx => exact (skin_eq _ _ _ (by omega)).symm
    exact h w he hw j (by omega)
lemma Rest.off {u:ℤ}{c:ℂ}(hz: Rest (fun _=>0) u c): c=0:= by rcases lt_or_ge u 0 with h|h; exact hz.bottom h; lift u to ℕ using h; simpa [reading] using (hz.home u (le_refl _)).symm
lemma Top_class {v:ℤ}(hp:G.Simple)(h: Lifting.Face wfield (Top G) (LE G v) v true): Class (LE G v) v:= by
    let F :=Top G; have hv : Solid true (Top G) 0:= by rw [Top_model]; exact blockSolid _ _ (TuneModel (crisp ..) 3) (ColorMod (realm G 1) 3) _
    have hh : SignedScope true (Top G):= by rw [Top_model]; exact choral _ (stance_model (observes G 1) 3)
    have hx (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E](w: Wire (Branch G Axis) E FourP): ContDiff ℝ ∞ (fieldVal (Top G) w):= by rw [Top_model]; exact all_smooth ..
    refine ⟨?_,?_, skin_form wfield v (fun E _ _ w _=> hx E w), fun s w hw=> skin_signed hh w hw s ⟩
    · exact ⟨fun l i j r hw=> skin_swap hv l r i j hw,fun w hw=> skin_ghost hv hw, fun w hw f=> skin_color hv hw (fun l _=> hx ℝ (ray l)) f,fun w hw=> skin_shadow hv hw (hx ℝ (ray w))⟩
    intro w hw; obtain ht:= table_fit h w (fun _=>hw); rw [show fieldVal _ (ray w)=fun _=>0 from funext fun x=> Top_closed hp (sail (ray w) x) (sail_course x (ray_course (b:=true) (fun _=>hw)) rfl)] at ht; exact Rest.off ht
lemma Top_first (G:Gauge) : Lifting.Face wfield (Top G) (LE G 3) 3 true:= Top_lead G 3 fun w he _ i hi=> by have h:= length_pay w; omega
lemma bulk_three (H:G.Simple) : Lifting.Face wfield (Top G) (LE G 4) 4 true:= Top_lead G 4 fun w he hw i hi=> by
    rw [face_here (Top_first G) hw i (by omega)]; split; · exact Mark.lower_three (Top_class H (Top_first G)) (by decide) _ (hw rfl) he
    rfl
-- Spheres leads target: other class with equal Lie token.
lemma top_align (h:G.Simple) {F:Law G} (H:Class F 4) (K:∀ i j k, token F i j k= token (LE G 4) i j k): EqualAt 3 F (LE G 4):=by
    intro w hw he; apply sub_eq_zero.mp; exact triple_zero (H.sub (Top_class h (bulk_three h))) (fun i j k=> (by simp [show token (F - LE G 4) i j k=token F i j k-token (LE G 4) i j k from rfl, K])) (by omega) _ hw he
end YM.MS.Menus
