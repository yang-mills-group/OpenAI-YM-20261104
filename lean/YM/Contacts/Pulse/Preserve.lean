import YM.Contacts.Pulse.Screen
/-! No self-loops: exact descent to a periodic cover with no winding error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pulse
open Function Set Filter RG Push.AbsoluteSums MergeProof
open scoped Classical BigOperators Topology NNReal
variable {ι κ X Y A B C D Q : Type*}
variable (p:X→Y)
-- array of connections: allow differing spaces
structure Trails (q:A→B)(G:X→ A→ℝ) (K:Y→B→ℝ) : Prop where
  row x : Scroll q (G x) (K (p x))
  col y : Scroll p (flip G y) (flip K (q y))
variable {p}
section
variable {F:Field (Option ι) X} {F':Field (Option ι) Y}
def expand_lift (x:X): (ι→X)≃Locked X (none:Option ι) x:= ⟨fun y=> ⟨vertex x y,rfl⟩,fun y=> y.val∘some,fun _=>rfl,fun a=> by rcases a with ⟨a,ha⟩; apply Subtype.ext; ext1 i; cases i <;> first | rfl | exact ha.symm ⟩ -- def
lemma Shadow.exempt (h:Shadow p F F')(x:X): Scroll (fun q:ι→X=> p∘q) (fun q=>F (vertex x q)) (fun q=> F' (vertex (p x) q)):= (h none x).across (expand_lift x) (expand_lift _) (fun y=> Subtype.ext (funext (fun i=> by cases i <;> rfl)))
def orientLocks (X:Type*) (e:κ≃ι) (i:κ)(x:X): Locked X i x ≃ Locked X (e i) x where
  toFun p:= ⟨p.val∘ e.symm,by simp [p.property]⟩
  invFun p:= ⟨p.val∘e,p.property⟩
  left_inv p:= Subtype.ext (funext fun i=>by simp)
  right_inv p:= Subtype.ext (funext fun i=>by simp)
lemma Shadow.replace {e:κ≃ ι}{F:Field ι X}{F':Field ι Y} (h:Shadow p F F'): Shadow p (fun x:κ→X=> F (x∘ e.symm)) (fun x:κ→Y=>F' (x∘ e.symm)):= by
  intro i x; exact (h (e i) x).across (orientLocks _ e _ _) (orientLocks _ e _ _) (fun y=> rfl)
end

-- factor left root -> available edge -> right tuple
def twin (x:(ι⊕κ)→X) (y z:X) := (vertex y (x∘ Sum.inl), z, x∘ Sum.inr)
def lineup (X:Type*) (κ:Type*) (i:ι)(x:X) : Locked X (Sum.inl i : ι⊕κ) x ×(X×X) ≃ Locked X (some i) x × (X× (κ→X)) where
  toFun p:=(⟨vertex p.2.1 (p.1.val ∘ Sum.inl),p.1.property⟩,p.2.2,p.1.val∘ Sum.inr)
  invFun p:=(⟨Sum.elim (p.1.val ∘ some) p.2.2,p.1.property⟩,p.1.val none,p.2.1)
  left_inv | ⟨p,y,v⟩ => Prod.ext (Subtype.ext (funext fun j=> by cases j<;> rfl)) rfl
  right_inv | ⟨p,x,y⟩=> Prod.ext (Subtype.ext (funext fun j=> by cases j<;> rfl)) rfl
private lemma flow_line {l:Range X}{G:X→X→ℝ}{b} (h:Track l G b)(x:X) : SumBudget (fun y=> ‖G x y‖) b := budget_mono (h.row x) (fun _=>norm_nonneg _) (fun _=> le_mul_of_one_le_right (norm_nonneg _) l.one_fee)
section
variable {F:Field (Option ι) X}{H:Field (Option κ) X}{G:X→ X→ℝ}{F':Field (Option ι) Y}{H':Field (Option κ) Y}{G':Y→Y→ℝ}
variable [Fintype κ] [Fintype ι]
private lemma forward_roll {l:Range X}{a b c} (h:Shadow p F F')(hp:Shadow p H H')(g:Trails p p G G')(hL:Rooted l F a)(hR: Rooted l H b)(hG:Track l G c) (i:ι)(x:X) : Scroll (roll p (Sum.inl i:ι⊕κ) x) (fun y=>stitch G F H y.val) (fun y=> stitch G' F' H' y.val):= by
  let U (t:Locked X (some i) x) (z:X× (κ→ X)):= G (t.val none) z.1*H (vertex z.1 z.2)
  let V (t:Locked Y (some i) (p x)) (z:Y× (κ→ Y)):= G' (t.val none) z.1*H' (vertex z.1 z.2)
  let A:= lineup X κ i x; let B:= lineup Y κ i (p x)
  let T (t:Locked X (some i) x × (X × (κ→X))):= F t.1.val* U t.1 t.2; let Q:= Prod.map (roll p (some i) x) (Prod.map p (fun x:κ→X=> p∘x))
  let f (z:Locked X (Sum.inl i:ι⊕κ) x ×(X×X)):= T (A z)
  have hf0 : Summable (fun z:Locked X (Sum.inl i:ι⊕κ) x ×(X×X)=> ‖F (vertex z.2.1 (z.1.val ∘ Sum.inl))*G z.2.1 z.2.2*H (vertex z.2.2 (z.1.val ∘ Sum.inr))‖):= by
    apply (budget_mono (stitching hG hL hR _ x) (fun _=>norm_nonneg _) (fun _=> le_mul_of_one_le_right (norm_nonneg _) (l.one_bill _))).2.1
  have hf: Summable f:= by simp_rw [mul_assoc] at hf0; exact hf0.of_norm
  have hU (x:Locked X (some i) x) : Summable (U x):= by
    apply Summable.of_norm; let y:=x.val none; unfold U; simp_rw [norm_mul]
    refine (Extra.Iteration.Cost.prod (g:=fun (x:X) (y:κ→X)=>‖H (vertex x y)‖) (flow_line hG y) ?_ hR.cash).2.1
    intro i; exact budget_map (hR.raw none i) (expand_lift i) (expand_lift i).injective (fun _=>rfl)
  have hK (a: Locked X (some i) x) : Scroll (Prod.map p (fun y:κ→X=> p ∘ y)) (U a) (V (roll p (some i) x a)) := (g.row (a.val none)).chain (k:=fun x y=>H (vertex x y)) (t:=fun x y=> H' (vertex x y)) (fun b=> hp.exempt b) (hU a)
  have hT: Scroll Q T (fun t=> F' t.1.val * V t.1 t.2):= (h (some i) x).chain (k:=U) (t:=V) hK (show Summable T from A.summable_iff.mp hf) 
  -- floor
  have hu : Scroll (Prod.map (roll p (Sum.inl i:ι⊕κ) x) (Prod.map p p)) f (fun z=> F' (vertex z.2.1 (z.1.val∘Sum.inl))*(G' z.2.1 z.2.2 * H' (vertex z.2.2 (z.1.val ∘ Sum.inr)))):= by
    let q:=Prod.map (roll p (Sum.inl i:ι⊕κ) x) (Prod.map p p); exact hT.across A B (q:=q) (fun c=> Prod.ext (Subtype.ext (funext (fun i=> by cases i<;>rfl))) rfl)
  unfold stitch; simp_rw [mul_assoc]; exact hu.collapse_fst hf

omit [Fintype κ] [Fintype ι] in
lemma stitch_turn (G:X→ X→ℝ)(F : Field (Option ι) X) (H : Field (Option κ) X) (x:ι⊕κ→X) : stitch G F H x = stitch (flip G) H F (x∘ Sum.swap):= by
  unfold stitch; rw [← (Equiv.prodComm X X).tsum_eq]; apply tsum_congr; rintro ⟨a,b⟩
  change F (vertex b (x∘Sum.inl)) * G b a * H (vertex a (x∘Sum.inr)) = H (vertex a (x∘Sum.inr)) * G b a * F (vertex b (x∘Sum.inl)); ring
lemma stitch_snapshot {l:Range X}{a b c} (h:Shadow p F F')(hp:Shadow p H H')(g:Trails p p G G')(hL:Rooted l F a)(hR: Rooted l H b)(hG:Track l G c) : Shadow p (stitch G F H) (stitch G' F' H'):= by
  intro i x; cases i with
  | inl i=>exact forward_roll h hp g hL hR hG i x
  | inr i=>
    have hx:= forward_roll hp h (show Trails p p (flip G) (flip G') from ⟨g.col,g.row⟩) hR hL hG.swap i x
    simp_rw [stitch_turn G,stitch_turn G']; exact hx.across (q:=roll p (Sum.inr i : ι ⊕ κ) x) (orientLocks X (Equiv.sumComm ι κ) (Sum.inr i) x) (orientLocks Y (Equiv.sumComm ι κ) (Sum.inr i) (p x)) (fun y=>rfl)
end
end YM.Pulse
