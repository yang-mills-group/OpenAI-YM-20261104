import YM.Contacts.Pulse.Root
/-! One joining Wick line or one loop. Absolute estimates are for arbitrary
finite valences on the cover or compatible finite systems. -/
noncomputable section
namespace YM.Pulse
open Function Set Finset Filter RG Push.AbsoluteSums
open scoped Classical Topology BigOperators NNReal
variable {ι κ X Y Z α β : Type*}

def vertex (a:X)(x:ι→X): Option ι→ X | none => a | some i=> x i
@[simp] lemma v_head (a:X)(x:ι→X): vertex a x none=a:=rfl
@[simp] lemma v_tail (a:X)(x:ι→X)(i) : vertex a x (some i)= x i:=rfl
abbrev Field (ι X : Type*):= (ι→X)→ℝ
def stitch (G:X→X→ℝ) (F : Field (Option ι) X) (H : Field (Option κ) X) (x:ι⊕κ→X) := ∑' p:X×X,F (vertex p.1 (x∘Sum.inl))*G p.1 p.2*H (vertex p.2 (x∘Sum.inr))
def loop (G : X→ X→ℝ)(F : Field (Option (Option ι)) X) (x : ι→ X):= ∑' p:X×X, G p.1 p.2 * F (vertex p.1 (vertex p.2 x))

structure Track (l : Range X)(G:X→X→ℝ)(b:ℝ) : Prop where
  cash : 0 ≤ b
  row (i:X) : SumBudget (fun x=> ‖G i x‖*l.step i x) b
  col (i:X) : SumBudget (fun x=> ‖G x i‖*l.step x i) b
variable {l:Range X}{F:Field (Option ι) X}{H:Field (Option κ) X}{W:Field (Option (Option ι)) X} {G:X→X→ℝ} {a b c:ℝ}
variable [Fintype ι][Fintype κ]

lemma Track.cap (h : Track l G b) (x y:X) : ‖G x y‖ ≤ b:= (le_mul_of_one_le_right (norm_nonneg _) l.one_fee).trans (budget_single (h.row _) _)
lemma Track.swap (h:Track l G b): Track l (flip G) b:= ⟨h.cash, fun i=> by simp_rw [Range.step,l.mirror i]; exact h.col i,fun i=> by simp_rw [Range.step,l.mirror _ i]; exact h.row i⟩

-- Paying bilinear join at a left-slot root. No floor for the coupling strip.
private lemma join_length (G:Range X) (x:ι⊕κ→X) (a b:X) : let Xo:=vertex a (x∘ Sum.inl); let Yo:= vertex b (x ∘ Sum.inr); G.bill x ≤ G.bill Xo * G.step a b * G.bill Yo:= by
  intro Xo Yo; have hA:= G.one_bill Xo; have hB:=G.one_bill Yo; have hC : 1≤G.step a b := G.one_fee
  let R:= G.bill Xo * G.step a b * G.bill Yo
  have hc:1 ≤G.bill Xo* G.step a b := one_le_mul_of_one_le_of_one_le hA hC
  have hp i j: G.step (x (Sum.inl i)) (x (Sum.inr j)) ≤ R:= by
    apply (G.triangle _ a _).trans
    unfold R; rw [mul_assoc]; gcongr
    · exact G.width Xo (some i) none
    exact (G.triangle _ b _).trans (mul_le_mul_of_nonneg_left (G.width Yo none (some j)) (by positivity))
  apply G.wide x (one_le_mul_of_one_le_of_one_le hc hB) (fun i j=>?_)
  rcases i with i|i <;> rcases j with j|j
  · apply (G.width Xo (some i) (some j)).trans; rw [mul_assoc]; exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hC hB)
  · exact hp _ _
  · unfold Range.step; rw [G.mirror (x (Sum.inr i))]; exact hp _ _
  exact (G.width Yo (some i) (some j)).trans (le_mul_of_one_le_left (by positivity) hc)

lemma vertex_bind (h:Rooted l F a)(x:X) : SumBudget (fun y:ι→ X=> ‖F (vertex x y)‖*l.bill (vertex x y)) a:= by
  apply budget_map (h.row none x) (fun y=> ⟨vertex x y,rfl⟩) _ fun _=> rfl
  intro p q h; exact funext fun i=> congr_fun (congr_arg Subtype.val h) (some i)

local notation "left" => Sum.inl
local notation "right" => Sum.inr
private lemma leftward (hG : Track l G a)(hF: Rooted l F b)(hH:Rooted l H c)(i:ι)(x:X) : SumBudget (fun p:Locked X (left i : ι⊕κ) x ×(X×X)=> ‖F (vertex p.2.1 (p.1.val ∘ Sum.inl))*G p.2.1 p.2.2*H (vertex p.2.2 (p.1.val ∘ Sum.inr))‖*l.bill p.1.val) (b*(a*c)):=by
  let lF (p:Locked X (some i) x) := ‖F p.val‖*l.bill p.val
  let t g v:= ‖G g v‖*l.step g v; let K (y:X)(p:κ→X):= ‖H (vertex y p)‖*l.bill (vertex y p)
  let f (p:Locked X (left i : ι⊕κ) x ×(X×X)) : Locked X (some i) x × (X× (κ→X)):= (⟨vertex p.2.1 (p.1.val ∘ Sum.inl),p.1.property⟩,p.2.2,p.1.val∘ Sum.inr)
  have ht (p: Locked X (some i) x): SumBudget (fun y:X× (κ→X)=> t (p.val none) y.1 * K y.1 y.2) (a*c):= by
    refine budget_rows _ (fun y:X=> t (p.val none) y*c) (fun y=> budget_scale (show 0≤ t (p.val none) y from (by unfold t; positivity)) (vertex_bind hH y)) ?_
    simpa only [t,mul_comm c] using budget_scale hH.cash (hG.row (p.val none))
  let s (p: Locked X (some i) x × (X×(κ→X))):= lF p.1 * (t (p.1.val none) p.2.1 * K p.2.1 p.2.2)
  have hs : SumBudget s (b*(a*c)) := by
    refine budget_rows _ (fun x=> lF x*(a*c)) (fun x=> budget_scale (hF.row .. |>.1 x) (ht x)) ?_
    simpa only [lF,mul_comm (a*c)] using budget_scale (mul_nonneg hG.cash hH.cash) (hF.row (some i) x)
  have hi:Injective f := by
    rintro ⟨p,u,v⟩ ⟨q,y,z⟩ he
    have hx : vertex u (p.val ∘Sum.inl)=vertex y (q.val∘Sum.inl):=congr_arg (fun w=> w.1.val) he
    have hv: v=z:= congr_arg (fun w=>w.2.1) he
    have hz: (p.val∘ right)=(q.val∘ right):= congr_arg (fun w=>w.2.2) he
    exact Prod.ext (Subtype.ext (funext (fun j=> Sum.rec (motive:=fun j=>p.val j=q.val j) (fun l=>congr_fun hx (some l)) (fun l=> congr_fun hz l) j))) (Prod.ext (congr_fun hx none) hv)
  apply budget_mono (budget_pull f hi hs) (fun _=>by positivity)
  rintro ⟨p,x',y⟩; dsimp only [s,f,t,K,lF]; simp only [norm_mul,v_head]
  apply le_trans (mul_le_mul_of_nonneg_left (join_length l p.val x' y) (by positivity)); ring_nf; exact le_rfl

-- Expose absolute in all bound claims. Allows subtraction / infinite-volume
-- interchanges before Wick projection.
lemma stitching (hG : Track l G a)(hF: Rooted l F b)(hH:Rooted l H c)(i:ι⊕κ)(x:X) : SumBudget (fun p:Locked X i x ×(X×X)=> ‖F (vertex p.2.1 (p.1.val ∘ Sum.inl))*G p.2.1 p.2.2*H (vertex p.2.2 (p.1.val ∘ Sum.inr))‖*l.bill p.1.val) (b*(a*c)):= by
  rcases i with i|i; exact leftward hG hF hH i x
  let C:= leftward hG.swap hH hF i x
  let f (y:Locked X (Sum.inr i : ι⊕κ) x ×(X×X)) : Locked X (left i : κ⊕ι) x × (X×X):= (⟨y.1.val ∘ Sum.swap, y.1.property⟩,y.2.swap)
  have he : Surjective (Sum.swap (α:=κ) (β:=ι)):= (Equiv.sumComm κ ι).surjective
  rw [show b*(a*c)=c*(a*b) by ring]; refine budget_map C f (fun p q hh=> Prod.ext ?_ ?_) ?_
  · exact Subtype.ext (funext (he.forall.mpr (fun j=> congr_fun (congr_arg (fun x=>x.1.val) hh) j)))
  · exact Prod.swap_injective (congr_arg (fun x=>x.2) hh)
  rintro ⟨p,y,z⟩; dsimp only [f]; rw [l.retrieve Sum.swap _ he]; change ‖_‖ * _= ‖H (vertex z ((p.val) ∘ Sum.inr))*G y z*F (vertex y (p.val ∘ Sum.inl))‖ * _; ring_nf

lemma stitch_root (hG : Track l G a)(hF: Rooted l F b)(hH:Rooted l H c): Rooted l (stitch G F H) (b*(a*c)) :=
  ⟨mul_nonneg hF.cash (mul_nonneg hG.cash hH.cash),fun i x=> budget_join (f:=fun x:Locked X i x=> fun p:X×X => F (vertex p.1 (x.val ∘ _))*G p.1 p.2*H (vertex p.2 (x.val ∘ Sum.inr))) (v:=fun x=>l.bill x.val) (fun _=>by positivity) (stitching hG hF hH i x) ⟩
lemma summable_stitch (hG : Track l G a)(hF: Rooted l F b)(hH:Rooted l H c)[Nonempty (ι⊕κ)] (u:ι⊕κ→X) : Summable (fun p:X×X=> ‖F (vertex p.1 (u∘ Sum.inl))*G p.1 p.2*H (vertex p.2 (u∘Sum.inr))‖) := by
  inhabit ι⊕κ; exact (summable_mul_right_iff (zero_lt_one.trans_le (l.one_bill u)).ne').1 ((stitching hG hF hH default (u default)).2.1.prod_factor ⟨u,rfl⟩)

lemma looping (hG : Track l G b)(hW:Rooted l W a) (i:ι)(x:X) : SumBudget (fun p:Locked X i x × (X×X)=>‖G p.2.1 p.2.2*W (vertex p.2.1 (vertex p.2.2 p.1.val))‖*l.bill p.1.val) (b*a):= by
  let u y z (f:ι→X):=vertex y (vertex z f);
  let φ (p:Locked X i x ×(X×X)): Locked X (some (some i)) x := ⟨u p.2.1 p.2.2 p.1.val,p.1.property⟩
  have hi : Injective φ := by rintro ⟨p,y,z⟩ ⟨q,s,t⟩ h; have hx:= congr_arg Subtype.val h; exact Prod.ext (Subtype.ext (funext fun i=> congr_fun hx (some (some i)))) (Prod.ext (congr_fun hx none) (congr_fun hx (some none)))
  apply budget_mono (budget_scale hG.cash (budget_pull _ hi (hW.row (some (some i)) x))) (fun _=>by positivity)
  rintro ⟨p,y,z⟩; rw [norm_mul, mul_assoc]; have hp : l.bill p.val ≤ l.bill (φ (p,y,z)).val := l.restrict (some ∘ some) (u y z p.val)
  apply mul_le_mul (hG.cap ..) (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (by positivity) hG.cash
lemma loop_root (hG : Track l G b)(hW:Rooted l W a) : Rooted l (loop G W) (b*a):=
  ⟨mul_nonneg hG.cash hW.cash,fun i x=> budget_join (v:=fun x:Locked X i x=>l.bill x.val) (fun _=>by positivity) (looping hG hW i x) ⟩
lemma summable_loop [Nonempty ι] (hG : Track l G b)(hW:Rooted l W a) (u:ι→X) : Summable (fun p:X×X=>‖G p.1 p.2*W (vertex p.1 (vertex p.2 u))‖):= by
  inhabit ι; exact (summable_mul_right_iff (zero_lt_one.trans_le (l.one_bill u)).ne').1 ((looping hG hW default (u default)).2.1.prod_factor ⟨u,rfl⟩)
end YM.Pulse
