import YM.Contacts.Pulse.Preserve
/-! A precise one-loop periodization charge at arbitrary inputs; no approximation
claim for stabilizers yet. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Set Filter Finset RG Push.AbsoluteSums MergeProof
open scoped Classical BigOperators Topology NNReal
variable {ι X Y A B : Type*} {b c d:ℝ}
lemma Scroll.filter {k:A→ B}{f:A→ℝ}{g t:B→ℝ}(h:Scroll k f g): Scroll k (fun i=> t (k i)*f i) (fun i=> t i*g i):= by
  intro i; rw [show (fun i=>t i*g i) i=t i*g i from rfl,h]; unfold cram; rw [←tsum_mul_left]; apply tsum_congr; intro x; simp only [x.property]
lemma winding_cost {l:Range X}{G:X→X→ℝ}{g:Y→Y→ℝ}{p:X→Y}(h:Track l G b)(hg:Trails p p G g)(hc:0<c) (hp:∀ x y:X, x≠y→p x=p y→ c ≤ l.step x y) (x y:X) : ‖g (p x) (p y) - G x y‖≤ b*(l.step x y /c):=by
  rw [hg.row]; unfold cram; let Y0:={i//p i=p y}; let a:Y0:=⟨y,rfl⟩; let V : Y0→ℝ:= fun i=> G x i
  let s (i:Y0):=‖G x i.val‖*l.step x i.val; let t:=l.step x y / c
  have hK:0≤t:= by unfold t; positivity
  have hs : SumBudget s b:= budget_pull _ Subtype.val_injective (h.row x)
  have hg' : Summable V:= (budget_mono hs (fun i=>norm_nonneg (V i)) (fun i=> le_mul_of_one_le_right (norm_nonneg _) l.one_fee)).2.1.of_norm
  rw [show G x y=V a from rfl];
  let f (i:Y0):= if i=a then V a else 0
  have h : Summable f:= hasSum_ite_eq a (V a)|>.summable
  change ‖(∑' i,V i)- V a‖≤_
  rw [show V a=∑' i,f i from ((hasSum_ite_eq a (V a)).tsum_eq).symm, ← hg'.tsum_sub h]
  have H : SumBudget (fun i=>‖V i-f i‖) (t*b):= by
    refine budget_mono (budget_scale hK hs) (fun i=>norm_nonneg _) fun i=> ?_
    unfold f; split
    next he=> have hu:=hs.1 i; rw [← he]; simp; exact mul_nonneg hK hu
    next he=>
      rw [sub_zero]; unfold s V; rw [mul_left_comm]; apply le_mul_of_one_le_right (norm_nonneg _) ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hc,one_mul]
      exact (hp y i (Ne.symm (fun eq=> he (Subtype.ext eq))) i.property.symm).trans ((l.triangle _ x _).trans_eq (by unfold Range.step; rw [l.mirror y x]))
  rw [mul_comm]; exact (norm_tsum_le_tsum_norm H.2.1).trans H.2.2

section
variable [Fintype ι] {l m o : Range X}{p:X→Y}
variable {G:X→X→ℝ}{H:Y→Y→ℝ}
variable {F:Field (Option (Option ι)) X} {K:Field (Option (Option ι)) Y}
-- windLoop: covariance may be growing in separation.
lemma wheel (hG : ∀ x y, ‖G x y‖≤ b*l.step x y)(hm : 0 ≤ b)(hF:Rooted m F d)(hc:∀ u:Option (Option ι)→X,l.bill u * o.bill u≤ m.bill u) (i:ι)(x:X) : SumBudget (fun p:Locked X i x × (X×X)=>‖G p.2.1 p.2.2*F (vertex p.2.1 (vertex p.2.2 p.1.val))‖*o.bill p.1.val) (b*d):= by
  let u y z (f:ι→X):=vertex y (vertex z f); let φ (p:Locked X i x ×(X×X)): Locked X (some (some i)) x := ⟨u p.2.1 p.2.2 p.1.val,p.1.property⟩
  have hi : Injective φ := by rintro ⟨p,y,z⟩ ⟨q,s,t⟩ h; have hx:= congr_arg Subtype.val h; exact Prod.ext (Subtype.ext (funext fun i=> congr_fun hx (some (some i)))) (Prod.ext (congr_fun hx none) (congr_fun hx (some none)))
  apply budget_mono (budget_scale hm (budget_pull _ hi (hF.row (some (some i)) x))) (fun _=>by positivity); rintro ⟨p,y,z⟩
  let v:=u y z p.val; change ‖G y z*F v‖ *o.bill p.val ≤ b*(‖F v‖ * m.bill v)
  have hp : o.bill p.val≤ o.bill v:= o.restrict (some∘some) v
  have hy: l.step y z≤ l.bill v:= l.width v none (some none);
  rw [norm_mul]; calc
    _ ≤ b*l.bill v*‖F v‖*o.bill v:= mul_le_mul (mul_le_mul_of_nonneg_right ((hG y z).trans (mul_le_mul_of_nonneg_left hy hm)) (norm_nonneg _)) hp (by positivity) (by positivity)
    _ = b*(‖F v‖*(l.bill v*o.bill v)):= by ring
    _ ≤ _:= by gcongr; exact hc _
lemma weather (hG : ∀ x y, ‖G x y‖≤ b*l.step x y)(hm : 0 ≤ b)(hF:Rooted m F d)(hc:∀ u:Option (Option ι)→X,l.bill u * o.bill u≤ m.bill u) : Rooted o (loop G F) (b*d):= ⟨mul_nonneg hm hF.cash,fun i x=> budget_join (v:=fun x:Locked X i x=>o.bill x.val) (fun _=>by positivity) (wheel hG hm hF hc i x)⟩
-- identify with periodic loop exactly (thus bound winding error subsequently via permissible l-vs-m)
def shunt (X:Type*) (i:ι)(x:X) : Locked X i x × (X×X) ≃ Locked X (some (some i)) x where
  toFun p:= ⟨vertex p.2.1 (vertex p.2.2 p.1.val),p.1.property⟩
  invFun p:= (⟨(p.val ∘ some) ∘ some,p.property⟩,p.val none,p.val (some none))
  left_inv _:=rfl
  right_inv p:= by apply Subtype.ext; funext i; rcases i with _|(_|x) <;> rfl
lemma snapshot_reflected (h : Shadow p F K)(hF:Rooted l F b)(he:∀ x y : Y,‖H x y‖ ≤ d)(hd:0≤ d): Shadow p (loop (fun x y=> H (p x) (p y)) F) (loop H K) := by
  intro i x; let V:= fun y:Locked Y (some (some i)) (p x)=> H (y.val none) (y.val (some none))
  let w:=h (some (some i)) x |>.filter (t:= V)
  let f (y:Locked X i x × (X × X)):= V (roll p (some (some i)) x (shunt X i x y))*F (shunt X i x y).val
  have hu: Summable f:= by
    apply Summable.of_norm; let t:= shunt X i x; simp_rw [f,norm_mul]; exact (budget_mono (budget_scale hd (budget_pull t t.injective (hF.raw (some (some i)) x))) (fun _=> mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _=> mul_le_mul_of_nonneg_right (he _ _) (norm_nonneg _))).2.1
  have he:= w.across (shunt X i x) (shunt Y i (p x)) (q:=Prod.map (roll p i x) (Prod.map p p)) (fun y=>Subtype.ext (by funext i; rcases i with _|(_|x) <;> rfl))
  exact he.collapse_fst hu
end
end YM.Pulse
