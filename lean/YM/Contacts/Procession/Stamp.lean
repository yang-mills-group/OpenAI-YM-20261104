import YM.Contacts.Procession.Drome
/-!
# Mark passage on lattice: root-wise and all-period winding

Raw (real ℝ) coefficients at OWN root.Brush before reset. Can inspect
rank zero through plot also. Cost of volume-independent output and of matching by period.
Shapes.Transaction. One use (no token from pert bulk of marks). Needs callers ascertain Period waits.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Procession.Xenon
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {α β ι:Type}{G:Gauge}{σ:ℝ≥0}{b c d:ℝ}{m:Side}{u B i k j r e:ℕ} {R:Row α α}{H:Row α β}{g:TableFee}
section
variable [Fintype α][Fintype β]
abbrev cardTime (α:Type) [Fintype α](x:ℝ) := (Fintype.card (Option α):ℝ)*x
def skies (α β:Type)[Fintype α][Fintype β](g:TableFee)(d c b:ℝ)(e j:ℕ):= pads (Option α) (Option β) j d (Pulse.sky (levity (cardTime α c) (stainCharge α g b)) e j)
def stalks (α β:Type)[Fintype α][Fintype β](g:TableFee)(d c b:ℝ)(e j:ℕ):= pads (Option α) (Option β) j d (Pulse.sky (lowland (cardTime α c) (cardTime α c) 0 (stainCharge α g b) 0) e j)
lemma occupation {x:α}{A:House (Node α)}{V:House (Co m α)}{F:Field (Fin i) (Node α)}(h:∀ i j, Two (voyageW m σ α) (A i j) (V i j) (g i j) 0)(hf:Rest (terrain σ α) (0,x) F b) (hR:R.strip σ c)(hc:0≤c)(hH:H.strip σ d)(hd:1≤ d): Two (voyageW m σ _) (hearth A (plane R) (Matrix.of (plane H)) F k e j) (hearth V (R.acts m) (H.acts m) (packing (lower m) F) k e j) (skies α β g d c b e j) (hush σ m * stalks α β g d c b e j):= by
   let X:=Option α; let Y:=Option β; let L:= stainCharge α g b; let S:= candy R; let Q:= piece H; have he:=ring_energy A F V g h hf; let v:=ringS k F A; let w:=cardTime α c; let C:= hush σ m; have hh := flight_stem (candy_leaf hR hc) hc; have ht: Track (terrain σ X) (plane S) w:= ⟨hh.left,hh.rows,hh.columns⟩; have hr:=torch (n:=m) ht (row_ship ..) (fun x y z=>by simp [plane,backpack]); let G:=ringS k (packing (lower m) F) V; have hs i j: Two (voyageW m σ X) (v i j) (G i j) (L i j) ((0:TableFee) i j):= he i j k
   have hT:= hoist_comp Q m (piece_leaf hH hd) (zero_le_one.trans hd) (completed hr hs e j); have hl : ∀ (k i j:ℕ), lowland w (C*w) 0 L 0 k i j= C*lowland w w 0 L 0 k i j:= fun k i j=>by simpa only [mul_zero,smul_zero] using wakeup_fees w w 0 C 0 L 0 k i j
   change Two _ _ _ _ (C*stalks α β g d c b e j); unfold S Q at hT; erw [period_Quiet, period_shade, footplane,shadeplane] at hT; convert hT using 1 <;> try rfl
   change C*stalks α β g d c b e j=pads X Y j d (Pulse.sky (lowland w (C*w) 0 L 0) e j); unfold stalks Pulse.sky; simp_rw [hl,←mul_sum]; unfold X Y L w pads; ring
end
private lemma phaseCheap {X:Type}(x:X)(u: Boys i X): fee (Range.cheap _) x u=1:=by rw [fee_basis]; apply le_antisymm _ ((Range.cheap X).one_bill _); exact ((Range.cheap X).wide _ le_rfl (fun i j=> le_rfl)) -- name
private lemma scoop_shr (T α:Type)[AddCommGroup T](a:T×α){F:Field (Fin (i+1)) (Live T α)}(h:Rooted (Range.cheap (Live T α)) F b): Rest (Range.cheap _) a (scoop F) ((i+1:ℕ)*b):= by
    let g:Field (Fin i) (T×α):= fun v=> F (focus 0 v); let e(v:Fin i→T×α): Locked (Live T α) (0:Fin (i+1)) (0,none):= ⟨focus 0 v,rfl⟩; -- use raw >= bound not equality.Lens
    have hl: Rest _ a g b:= budget_map (h.raw (0:Fin (i+1)) (0,none)) _ (show Injective e from fun v w h=> (focus_root _ _ (0:T) _ (congr_arg Subtype.val h)).2) (fun i=> by rw [phaseCheap,mul_one])
    convert hl.smul ((i+1:ℕ):ℝ) using 1; · ext i; rw [scoop, Pi.smul_apply, Pi.smul_apply,nsmul_eq_mul]; rfl
    congr 1; exact (Real.norm_of_nonneg (by positivity)).symm
-- include Rest, not merely Two cheap
structure Alive (σ:ℝ≥0)(b c:ℝ)(v:α) (F:Field (Fin i) (Node α))(m:Side)(G:Field (Fin i) (Co m α)):Prop where
   room : Rest (terrain σ α) (0,v) F b
   portrait : Rest (Range.cheap _) (0,v) G b
   far : Rest (Range.cheap _) (0,v) (G-packing (lower m) F) c
lemma aware {F:Field (Fin (i+1)) (Node (Option α))}{V:Field (Fin (i+1)) (Co m (Option α))}(H:Two (voyageW m σ _) F V b c) (x:α) : Alive σ ((i+1:ℕ)*b) ((i+1:ℕ)*c) x (scoop F) m (scoop V) := by
   obtain ⟨P,hP,h⟩:=H.owes; refine ⟨homing_credit H.ground, scoop_shr (Site m) α (0,x) H.seats,?_⟩; rw [← home m hP, show scoop V - scoop P = scoop (V-P) from funext fun x=> by simp [scoop, smul_sub]]; exact scoop_shr _ _ (0,x) h -- invalid
-- full version explicit with film cost
variable [Fintype α][Fintype β]
theorem reading_block {x:α}{A: House (Node α)}{V:House (Co m α)}{F:Field (Fin i) (Node α)}(h:∀ i j, Two (voyageW m σ α) (A i j) (V i j) (g i j) 0)(hf: Rest (terrain σ α) (0,x) F b)(hR:R.strip σ c)(hc:0≤c)(hH:H.strip σ d)(hd:1≤ d)(y:β)(hV:Snug V)(he:e < B)(hP:Poem F)(hi:i≤B): Alive σ ((j+1:ℕ)* skies α β g d c b (B+e) (j+1)) ((j+1:ℕ)*(hush σ m * stalks α β g d c b (B+e) (j+1))) y (porch A (plane R) (Matrix.of (plane H)) F B e j) m (rose V (R.acts m) (H.acts m) (packing (lower m) F) e j):= by rw [← door (B:=B) _ _ _ hV hi he (Shuttle.poetic F hP (lower m)) ]; exact aware (occupation h hf hR hc hH hd) y
end YM.Contacts.Procession.Xenon
