import YM.MSbar.Domain.Account
/-! Kernel support linear algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Dim Symbol Super Loops MeasureTheory Function Set Filter
open scoped Topology BigOperators Classical ContDiff
variable {C:Type}{n i j:ℕ}{U:Set ℂ}{V: Edition C}{F G :Functionals C}{X Y:Links C}{d:Bit}
namespace Full
lemma add (h:Full U j V d F)(H:Full U j V d G): Full U j V d (F+G):=
    ⟨h.licensed.add H.licensed,(h.total.add H.total).quiet,fun z hz k a p s t=> (h.colors z hz k a p s t).add (H.colors z hz k a p s t),fun z hz k=>(h.span z hz k).add (H.span z hz k)⟩
lemma scale (h:Full U j V d F)(c:ℂ): Full U j V d (c•F):=
    ⟨h.licensed.scale c,(h.total.scale c).quiet,fun z hz k a p s t=>(h.colors z hz k a p s t).scale c, fun z hz k=> (h.span z hz k).scaling c⟩
lemma neg (h:Full U j V d F):Full U j V d (-F):=by simpa only [neg_smul,one_smul] using h.scale (-1:ℂ)
lemma sub (h:Full U j V d F)(H:Full U j V d G): Full U j V d (F-G):= by rw [sub_eq_add_neg]; exact h.add H.neg
lemma zero (U:Set ℂ) (j:ℕ) (W:Edition C)(d:Bit): Full U j W d 0 :=⟨Eligible.zero,fun _ _ _=> Quiet.zero, fun _ _ _ _ _ _ _=> Dim.One.zero,fun _ _ _=> Homogeneous.zero⟩
lemma sum {T:Type*} (I:Finset T){F:T→Functionals C}(h:∀ i∈I,Full U j V d (F i)): Full U j V d (∑ i∈I,F i):=by induction I using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zero .. | insert i s he ih=>rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h _ (Finset.mem_insert_of_mem hj))
lemma shrink (h:Full U j V d F){W:Set ℂ}(hw:W⊆U): Full W j V d F:=⟨h.licensed.upon hw,fun _ hz=>h.quiet _ (hw hz),fun _ hz=> h.colors _ (hw hz),fun _ hz=>h.span _ (hw hz)⟩
lemma rechoose (h:Full U j V d F)(hl:U≠univ) (k:ℕ): Full U k V d F:=⟨⟨h.licensed.natural,by introv H; exact (h.licensed.ev _ _ H).ignore hl _⟩,h.quiet,h.colors,h.span⟩
lemma congr (h:Full U j V d F)(hu:IsOpen U)(he:∀ z∈U,F z=G z): Full U j V d G:=⟨h.licensed.agrees hu he,fun z hz=> he z hz ▸ h.quiet z hz,fun z hz=> he z hz ▸ h.colors z hz, fun z hz=> he z hz ▸ h.span z hz⟩
end Full
namespace Pilot
lemma add (h:Pilot U j V d X)(H:Pilot U j V d Y): Pilot U j V d (X+Y):=
    ⟨fun a b=> (h.cost a b).add (H.cost a b), fun a b he z hz i k=>by simp [lines,show X z i _ _ _ =0 from h.parity a b he z hz i k,show Y z i _ _ _=0 from H.parity a b he z hz i k],fun a b z hz i p q=> (h.uniformL a b z hz i p q).add (H.uniformL a b z hz i p q), fun a b z hz i p q=> (h.uniformR a b z hz i p q).add (H.uniformR a b z hz i p q)⟩
lemma scale (h:Pilot U j V d X)(c:ℂ): Pilot U j V d (c•X):=⟨fun a b =>(h.cost a b).scale c,fun a b he z hz i k=>by simp [lines,show X z i _ _ _ =0 from h.parity a b he z hz i k],fun a b z hz i p q=> (h.uniformL a b z hz i p q).scale c,fun a b z hz i p q=> (h.uniformR a b z hz i p q).scale c⟩
lemma zero (U:Set ℂ) (j:ℕ)(W:Edition C)(d:Bit): Pilot U j W d 0:= ⟨fun a b=> Eligible.zero,fun _ _ _ _ _ _ _=>rfl,fun _ _ _ _ _ _ _=> Dim.One.zero,fun _ _ _ _ _ _ _=> Dim.One.zero⟩
end Pilot

namespace Band
variable {c b : ℝ}
lemma add (hp:Band U X c)(hh:Band U Y c) : Band U (X+Y) c:= fun z hz m a b v hv=>by simp [hp z hz m a b v hv,hh z hz m a b v hv]
lemma mon (hp:Band U X c)(hb:c ≤ b):Band U X b:= fun z hz m a b x hx=> hp z hz _ _ _ _ (hb.trans_lt hx)
lemma scale (hp:Band U X c)(b:ℂ) : Band U (b•X) c:= fun z hz m a c v hv=>by simp [hp z hz m a c v hv]
end Band
end YM.MSbar.Domain
