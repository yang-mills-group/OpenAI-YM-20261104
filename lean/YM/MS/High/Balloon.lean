import YM.MS.High.Rigid
/-!
# Recover transformation with color independent momentum

`splice` multilinear. Use `spool` (colors fixed externally) convenient extension at rank.
`color_paths` supports Curator. Needed before transporting symmetries of canonical bulk.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm Color
open scoped Topology ContDiff
variable {G : Gauge} {A E P:Type} {F: Score G A P}
    {f : Law G} {M : Reading G} {w : List (Lane4 G)} {b : Bool} {d h:ℤ}
-- color visit by `Same`
def undye (w : List (Note G A P)) := w.map fun i=> (i.1.1,i.2)
abbrev paint (w v: List (Note G A P)) : Prop := undye w=undye v
@[simp] lemma dye (i: Note G A P) l : undye (i::l)=(i.1.1,i.2)::undye l:= rfl
lemma dye_next (i : Note G A P) {l k: List (Note G A P)} (c:CI G) (h : paint l k): paint (setLeg i c::l) (i::k) := by unfold paint at *; simp [setLeg,h]

lemma paint_len (u v : List (Note G A P)) (h : paint u v) : u.length=v.length:= by simpa [undye] using congr_arg List.length h

variable [NormedAddCommGroup P]
lemma paint_course {u v : List (Note G A P)} (h : paint u v) (hx : Course b u): Course b v:= by
   intro p; specialize hx p
   have hm (T : List (Note G A P)): net (undye T)=net T:=by unfold net undye; rw [List.map_map]; rfl
   exact (hm v).symm.trans ((congr_arg net h).symm.trans ((hm u).trans hx))

omit [NormedAddCommGroup P] in
lemma dye_dim {u v: List (Note G A P)} (h : paint u v) : fieldDim wfield u=fieldDim wfield v:= by
   have hv (u : List (Note G A P)) : fieldDim wfield u= fieldDim (fun i=> (dim i:ℤ)) (undye u):=by unfold fieldDim undye; rw [List.map_map]; rfl
   rw [hv u,hv v, show undye u=undye v from h]

-- multilinear extension

-- note when scaling in x, shuttle with colors and keep momenta adapted
lemma loop_color (u : G.El) {A : Type} (x:ℝ) (w : List (Note G A P)) [NormedSpace ℝ P] (f:Score G A P) : repeatC u f (sail (ray w) x)=repeatC u (fun v=>f (sail (ray v) x)) w:= by
   induction w generalizing f with
   | nil=> rfl
   | cons i w ih=> simp only [sail_cons, ray, List.map_cons] at *; rw [repeat_cons,repeat_cons]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [ih]; dsimp only; congr! 1
omit [NormedAddCommGroup P] in
lemma paint_zero (k:G.El) (u : List (Note G A P)) (h: ∀ l, paint l u→ F l=0): repeatC k F u=0:= by
    induction u generalizing F with
    | nil=> exact h [] rfl
    | cons i v ih=> rw [repeat_cons]; exact Finset.sum_eq_zero fun j _=> mul_eq_zero_of_right _ (ih (fun l he=>h _ (dye_next i _ he)))
omit [NormedAddCommGroup P] in
lemma paint_congr (k:G.El) (u:List (Note G A P)) {F H : Score G A P} (h : ∀ l, paint l u→ F l=H l) : repeatC k F u=repeatC k H u:= by
   have hm:= paint_zero k u (F:=F-H) (fun l hL=> sub_eq_zero.mpr (h l hL)); rw [map_sub, Pi.sub_apply] at hm; exact sub_eq_zero.mp hm

omit [NormedAddCommGroup P] in
lemma repeat_diff (k:G.El) (w : List (Note G A P)) {U:ℝ→ Score G A P} (hf: ∀ v, paint v w → ContDiff ℝ ∞ fun x => U x v): ContDiff ℝ ∞ (fun x=>repeatC k (U x) w):= by
    induction w generalizing U with
    | nil=> exact hf [] rfl
    | cons i w ih=> simp_rw [repeat_cons]; exact ContDiff.sum (fun c _=> contDiff_const.mul (ih (fun l h=>hf _ (dye_next i _ h))))
omit [NormedAddCommGroup P] in
lemma repeat_reader (u:G.El) (j:ℕ) {w:List (Note G A P)} {F:ℝ→ Score G A P} (hf : ∀ l, paint l w→ ContDiff ℝ ∞ fun x=>F x l): reading j (fun x=>repeatC u (F x) w)= repeatC u (fun w=>reading j (fun x=>F x w)) w:= by
   induction w generalizing F with
   | nil=>rfl
   | cons i w ih=>
                    simp_rw [repeat_cons]
                    have he k l (h : paint l w): ContDiff ℝ ∞ fun x=>F x (setLeg i k::l):=hf _ (dye_next i _ h)
                    rw [read_sum (fun k _=>contDiff_const.mul (repeat_diff u w (U:=fun x=>D (setLeg i k) (F x)) (he k)))]; simp_rw [read_const]; apply Finset.sum_congr rfl; intro j _; rw [ih (F:=fun x=>D (setLeg i j) (F x)) (he j)]; rfl
omit [NormedAddCommGroup P] in
lemma repeat_lim {F : ℝ→ Score G A P} {K : Score G A P} {w:List (Note G A P)} (u:G.El) (h : ∀ l, paint l w → Tendsto (fun x=> F x l) atTop (𝓝 (K l))) : Tendsto (fun x=>repeatC u (F x) w) atTop (𝓝 (repeatC u K w)):= by
   induction w generalizing F K with
   | nil=> exact h [] rfl
   | cons i w ih=> simp_rw [repeat_cons]; exact tendsto_finsetSum Finset.univ fun k _=> (ih (F:=fun x=> D (setLeg i k) (F x)) (K:=D (setLeg i k) K) (fun l he=> h _ (dye_next i _ he))).const_mul _
lemma skin_color (hs : Solid b f d) (hw:Course b w) (hp:∀ u, paint u w→ContDiff ℝ ∞ fun x=> f (sail (ray u) x)) (k:G.El) : repeatC k (skin wfield h f) w=skin wfield h f w:= by
   rcases lt_or_ge h (fieldDim wfield w) with he|he
   · have hv u (hu : paint u w): skin wfield h f u=0:= by unfold skin; rw [dye_dim hu,if_neg he.not_ge]
     rw [paint_zero k w hv,hv w rfl]
   let L u x:= f (sail (ray u) x); let P:= (h-fieldDim wfield w).toNat
   have hL i (hp : paint i w) : skin wfield h f i= reading P (L i):=by unfold skin; rw [dye_dim hp,if_pos he]; rfl
   rw [hL w rfl,paint_congr k w hL,← repeat_reader k P (F:=fun x t=>L t x) hp]; congr 1; ext x; rw [show repeatC k (fun t=> L t x) w=_ from (loop_color k x w f).symm]; exact hs.color _ (sail_course x (ray_course hw)) k
end YM.MS.High
