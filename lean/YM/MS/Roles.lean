import YM.MS.Color.Components
/-!
# Legs with spacetime momentum; exchange, charges and reality

`pin` is for proving classification under planar tests only. Off-shell
with group operations preserving the mid-point convention. Retain strict rank
bounds for all Taylor coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Function Filter Set Finset Plane Real Koszul Wire
open scoped Topology ContDiff
variable {P D A : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
namespace Plane
-- `Ranked` (one) & `Upper` (ceiling). At bulk need only conserved.
abbrev Ranked (b:Bool) (r : ℕ) (f: Row A P ℂ):= ∀ w, Course b w → w.length≠r→ f w=0
abbrev Upper (b:Bool) (r : ℕ) (f: Row A P ℂ):= ∀ w, Course b w → r<w.length → f w=0
variable {b : Bool} {w : Wire A P P} {p : Sector A} {f g : Row A P ℂ}
omit [NormedSpace ℝ P] in
lemma course_swap (b) (l k : Legs (Mode A P)) (i j : Mode A P) (h : Course b (l++i::j::k)): Course b (l++j::i::k):= by intro hb; simpa only [net_append,net_cons,add_left_comm (_:P)] using h hb
namespace Form
variable {d : ℤ} {m : A → ℤ}
lemma zero : Form (0 : Row A P ℂ) m d b:= fun (_ : Type) _ _ _ _=> form_zero _
lemma scalar (c:ℂ) (h : Form f m d b): Form (c • f) m d b:= fun (E:Type) _ _ w hw=> (h E w hw).scalar c
lemma add (h : Form f m d b) (H : Form g m d b): Form (f+g) m d b:= fun (E:Type) _ _ w hw=> (h E w hw).add (H E w hw)
lemma neg (h : Form f m d b): Form (-f) m d b:=by simpa using h.scalar (-1:ℂ)
lemma sub (h : Form f m d b) (H : Form g m d b): Form (f-g) m d b:=by simpa [sub_eq_add_neg] using h.add H.neg
lemma no_tall (h : Form f m d b) (w : Legs (Mode A P)) (hw : Course b w) (hl : d<fieldDim m w): f w=0:= by
    have he := (h ℝ (ray w) (ray_course hw)).charge (show d-fieldDim m _<0 from sub_neg_of_lt (by rw [ray_dim]; exact hl))
    exact (congr_arg f (ray_sail w).symm).trans (congr_fun he 1)
lemma level (h : Form f m d b) (w : Legs (Mode A P)) (hw : Course b w) (hl : fieldDim m w=d) : f w=f (w.map fun i => (i.1,0)) := by
    let Q:=ray w; have he : d-fieldDim m Q=0:= by dsimp only [Q]; rw [ray_dim,hl,sub_self]
    have hs: f (sail Q ((0:ℝ)•1))=(0:ℝ)^(d-fieldDim m Q)•f (sail Q 1):= (h ℝ Q (ray_course hw)).scale 0 1
    rw [he] at hs; rw [show sail Q 1=w from ray_sail w] at hs; simpa only [zpow_zero,one_smul,zero_smul,Q,ray_go] using hs.symm
end Form
end Plane
namespace Landau
variable {G : Gauge}
variable {f g : Score G D P} {h: ℤ} {b : Bool}
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma solo_add (u:G.El) (w : Legs (Note G D P)) : solo u w (f+g) = solo u w f+solo u w g:= by
   induction w generalizing f g with
   | nil=>rfl
   | cons a l ih=>
       rcases a with ⟨⟨i,k⟩,p⟩; simp only [solo, Pi.add_apply]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun j _=>?_);
       rw [show (fun l=> f (((i,j),p)::l)+g (((i,j),p)::l))= (fun l=> f (((i,j),p)::l)) + (fun l=> g (((i,j),p)::l)) from rfl,ih,mul_add]
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma solo_mul (u:G.El) (c:ℂ) (w : Legs (Note G D P)) : solo u w (c • f)= c * solo u w f:= by
   induction w generalizing f with
   | nil=> rfl
   | cons a l ih=>
       rcases a with ⟨⟨i,k⟩,p⟩; simp only [solo]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j h=> ?_)
       rw [show (fun l=> (c • f) (((i,j),p)::l)) = c • (fun l=> f (((i,j),p)::l)) from rfl, ih]; ring
omit [NormedSpace ℝ P]
lemma solid_zero : Solid b (0:Score G D P) h:= ⟨fun _ _ _ _ _=> Eq.symm (mul_zero _), fun _ _ _=>rfl, fun w hw a=>by simpa using solo_mul (P:=P) (f:=0) a 0 w, fun _ _=>(star_zero _).symm⟩
namespace Solid
lemma add (hf:Solid b f h) (hg:Solid b g h) : Solid b (f+g) h where
    symm l i k r h:=by simp only [Pi.add_apply,mul_add]; rw [hf.symm l i k r h, hg.symm l i k r h]
    ghost w h hp:= by rw [Pi.add_apply,hf.ghost w h hp,hg.ghost w h hp,add_zero]
    color w h a:= by rw [solo_add,hf.color _ h a,hg.color _ h a]; rfl
    real' w h:= by rw [Pi.add_apply,Pi.add_apply,star_add,hf.real' w h,hg.real' w h]
lemma scalar (c: ℝ) (hf:Solid b f h) : Solid b ((c:ℂ) • f) h where
    symm l i k r h:=by simp only [Pi.smul_apply,smul_eq_mul]; rw [hf.symm l i k r h,mul_left_comm]
    ghost w h hp := by simp [hf.ghost w h hp]
    color w h a := by rw [solo_mul,hf.color]; rfl; exact h
    real' w h:= by rw [Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,hf.real' w h,star_mul']; simp
lemma neg (hf:Solid b f h): Solid b (-f) h:= by simpa using hf.scalar (-1)
lemma sub (hf:Solid b f h) (hg:Solid b g h): Solid b (f-g) h:=by simpa [sub_eq_add_neg] using hf.add hg.neg
end Solid
namespace SignedScope
variable {f g : Score G Axis (Momentum Axis)}
lemma add (hf : SignedScope b f) (hg : SignedScope b g): SignedScope b (f+g):=fun k w h=> by rw [Pi.add_apply,Pi.add_apply,mul_add, hf k w h,hg k w h]
lemma scalar (hf : SignedScope b f) (c:ℂ): SignedScope b (c • f) := fun k w h=> by simp only [Pi.smul_apply,smul_eq_mul]; rw [mul_left_comm, hf k w h]
lemma neg (hf : SignedScope b f): SignedScope b (-f):=by simpa using hf.scalar (-1)
lemma sub (hf : SignedScope b f) (hg : SignedScope b g): SignedScope b (f-g):=by simpa [sub_eq_add_neg] using hf.add hg.neg
end SignedScope
end Landau
end YM.MS
