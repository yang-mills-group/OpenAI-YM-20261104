import YM.XSpace.Walkways

/-!
# Cover lookup of our invariant tangent stencils

General enough to paint with winding offsets on torus or cover. All statements use
`tool j x : Physical Shift`, no r-dependence hidden inside coefficients. θ-symmetry
*not* presumed on UF for any statement in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Outline
open Function JetGauge Lattice RG Wilson Labels Source Source.Drops Chart2 Next.Rank.Normal
open Finsupp MvPolynomial
open scoped Topology BigOperators
variable {G:Gauge} {n d:ℕ} {R Q K:Type*} [Group K] [AddCommGroup R] [One R] [AddCommGroup Q] [One Q]
structure Chart (R Q:Type*) [AddCommGroup R] [One R] [AddCommGroup Q] [One Q] where
  site : Four R → Four Q
  next (i d): site (i+step d)= site i+step d
namespace Chart
variable (c:Chart R Q)

def lug (p:Four R):Chart R R:=⟨(fun x=> x+p),fun _ _=> add_right_comm ..⟩
def wreath (n:Side):Chart ℤ (Per n):=⟨wrap n,fun _ _=>by simp⟩
def atop {R Q S:Type*} [AddCommGroup R] [One R] [AddCommGroup Q] [One Q] [AddCommGroup S] [One S] (f:Chart Q S)(g:Chart R Q):Chart R S:=⟨f.site ∘ g.site, fun i d=>by simp [g.next,f.next]⟩
def shift (x:Four Q): Chart R Q:= (lug x).atop c
lemma shift_at (x:Four R)(a:Four Q): (c.shift a).site x=c.site x+a:=rfl
abbrev move (i:Edges2 R): Edges2 Q:=(c.site i.1,i.2)
def roll : Rollers (Edges2 R) G → Rollers (Edges2 Q) G:= Prod.map c.move id
def input (A:LogLinks Q G): LogLinks R G := A ∘ c.move
def pull : St R G →ₐ[ℂ] St Q G:= rename c.roll
lemma pull_point (A:LogLinks Q G)(p:St R G): pit A (c.pull p)=pit (c.input A) p:= renamed ..
lemma site_prev (i d): c.site (i-step d)=c.site i-step d:=eq_sub_of_add_eq (by rw [← c.next,sub_add_cancel])
lemma site_step (i)(d:Step): c.site (i+d.vec)=c.site i+d.vec:=by cases d with| mk t h=> cases h; exact c.next ..; simpa only [Step.vec,if_true,← sub_eq_add_neg] using c.site_prev i t
lemma stop_moves (i)(p:Walk): c.site (stop i p)=stop (c.site i) p:=by induction p generalizing i <;> simp_all [stop,c.site_step]
lemma carries (u:Links Q K)(x:Four R)(w:Walk):travel (u ∘ c.move) x w=travel u (c.site x) w:=by
  induction w generalizing x with
  | nil=>rfl
  | cons d w ih=>rw [travel,travel,ih,c.site_step]; congr 1; rcases d with ⟨t,h|h⟩; rfl; simp [Step.read,Step.used,c.site_prev,move]
lemma onto_face (A:LogLinks Q G) (p:Face R): faceValue (native (c.input A)) p=faceValue (native A) (c.site p.1,p.2):= c.carries (native A) p.1 (square p.2.val.1 p.2.val.2)
lemma onto_round (A:LogLinks Q G) (s:Slot)(x:Four R): roundTrip s x (native (c.input A))=roundTrip s (c.site x) (native A):=by
  unfold roundTrip; rw [onto_face,show travel (native (c.input A)) _ _= _ from c.carries (native A) x s.walk,c.stop_moves x s.walk]
lemma pflux (A:LogLinks Q G)(p:Face R): linearFace p (c.input A)=linearFace (c.site p.1,p.2) A:=by rw [← face_a p _ 0,← face_a _ _ 0]; exact congr_arg Drift.a (c.onto_face A p)
lemma v3 (p:Face R): c.pull (V3 G p)= V3 G (c.site p.1,p.2):=by apply same; intro A; rw [pull_point,price_at,price_at,diagnostic,diagnostic,c.pflux,acc,c.onto_face]; rfl

variable {H:Hol G}(S:Survey G H d)
lemma fund (x:Four R)(A:LogLinks Q G): primary S x (c.input A)= primary S (c.site x) A ∧ secondary S x (c.input A)=secondary S (c.site x) A:=by
  have he : spectra S x (c.input A)= spectra S (c.site x) A:=by
    funext i; change take1 _ _ _=take1 _ _ _; rw [← round_a (S.looks i) _ _ 0,← round_a (S.looks i) _ _ 0]; exact congr_arg Drift.a (c.onto_round A (S.looks i) _)
  have hx : accent S x (c.input A)= accent S (c.site x) A:= funext fun i=> congr_arg Drift.c (c.onto_round A _ x)
  rw [primary_at,primary_at,secondary,secondary,he,hx]; trivial
lemma pull0 (x:Four R)(p:Labels.Pol G): c.pull (p0 S x p)= p0 S (c.site x) p:=same fun A=>by rw [pull_point,awake0,awake0,(c.fund S x A).1]
lemma pull1 (x:Four R)(p:Labels.Pol G): c.pull (p1 S x p)= p1 S (c.site x) p:=same fun A=>by rw [pull_point,awake1,awake1,(c.fund S x A).1,(c.fund S x A).2]
end Chart
end YM.XSpace.Outline
