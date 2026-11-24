import YM.Contacts.Pulse.Vision
/-! Simultaneous comparison budgets on connected operations. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Filter RG Finset
open scoped Topology BigOperators Classical NNReal
variable {ι κ X Y : Type*}{l m:Range X}{G H:X→X→ℝ}{a b c d e v : ℝ}

-- include non-asymptotic linearity for readable rank (never cancellations at rank zero)
variable [Fintype ι][Fintype κ]
section Loop
variable {F K:Field (Option (Option ι)) X}
lemma loop_less [Nonempty ι] (g:Track l G a)(f:Rooted l F b)(h:Rooted l K c): loop G (F-K)= loop G F-loop G K:= by
  ext1 x; simp only [loop,Pi.sub_apply,mul_sub]
  exact (summable_loop g f x|>.of_norm).tsum_sub (summable_loop g h x|>.of_norm)
-- allow periodicized covariance bounded
lemma loop_cost (h:∀ x y, ‖G x y‖≤ a)(hf:Rooted l F b) (ha:0 ≤ a) (i:ι) (x:X): SumBudget (fun p:Locked X i x × (X×X)=>‖G p.2.1 p.2.2 * F (vertex p.2.1 (vertex p.2.2 p.1.val))‖*l.bill p.1.val) (a*b):= by
  apply wheel (l:=Range.cheap X) ?_ ha hf
  · intro u; apply le_of_eq; rw [show (Range.cheap X).bill u=1 from ?_,one_mul]; exact le_antisymm ((Range.cheap _).wide u le_rfl (fun _ _=> le_rfl)) ((Range.cheap _).one_bill _)
  intro x y; rw [show (Range.cheap X).step _ _=1 from rfl,mul_one]; exact h x y
lemma loop_attains (h:∀ x y, ‖G x y‖≤ a)(hf:Rooted l F b) (ha:0 ≤ a): Rooted l (loop G F) (a*b):= ⟨mul_nonneg ha hf.cash,fun i x=> budget_join (v:=fun p:Locked X i x=>l.bill p.val) (fun _=>by positivity) (loop_cost h hf ha i x)⟩
lemma loop_meets [Nonempty ι] (h:∀ x y, ‖G x y‖≤ a)(hf:Rooted l F b) (ha:0 ≤ a) (u:ι→X) : Summable (fun p:X×X=> G p.1 p.2 * F (vertex p.1 (vertex p.2 u))):= by
  apply Summable.of_norm; inhabit ι; exact (summable_mul_right_iff (zero_lt_one.trans_le (l.one_bill u)).ne').mp ((loop_cost h hf ha default (u default)).2.1.prod_factor ⟨u,rfl⟩)
lemma loop_line [Nonempty ι] (g:∀ i j,‖G i j‖≤a)(h:∀ i j,‖H i j‖≤b)(hf:Rooted l F c)(ha:0≤a)(hb:0≤b): loop (G-H) F=loop G F-loop H F:= by ext1 x; simp only [loop,Pi.sub_apply,sub_mul]; exact (loop_meets g hf ha x).tsum_sub (loop_meets h hf hb x)
end Loop
section Join
variable {F K:Field (Option ι) X}{P Q:Field (Option κ) X}
lemma coldF [Nonempty (ι⊕κ)] (g:Track l G a)(h:Rooted l F b)(k: Rooted l K c)(f: Rooted l P d) : stitch G (F-K) P=stitch G F P - stitch G K P:= by ext1 x; simp only [stitch,Pi.sub_apply,sub_mul]; exact (summable_stitch g h f x|>.of_norm).tsum_sub (summable_stitch g k f x|>.of_norm)
lemma coldL [Nonempty (ι⊕κ)] (g:Track l G a)(h:Rooted l F b)(f: Rooted l P d)(k:Rooted l Q c) : stitch G F (P-Q)=stitch G F P - stitch G F Q:= by ext1 x; simp only [stitch,Pi.sub_apply,mul_sub]; exact (summable_stitch g h f x|>.of_norm).tsum_sub (summable_stitch g h k x|>.of_norm)
lemma coldC [Nonempty (ι⊕κ)] (g:Track l G a)(k:Track l H c)(h:Rooted l F b)(f: Rooted l P d): stitch (G-H) F P=stitch G F P - stitch H F P:= by ext1 x; simp only [stitch,Pi.sub_apply,mul_sub,sub_mul]; exact (summable_stitch g h f x|>.of_norm).tsum_sub (summable_stitch k h f x|>.of_norm)
lemma stitch_diff [Nonempty (ι⊕κ)] {x y:ℝ}
    (g:Track l G a)(h:Track l H a)(he:Track l (G-H) d)
    (hf:Rooted l F b)(hk:Rooted l K b)(hp:Rooted l P c)(hq:Rooted l Q c)(x₀:Rooted l (F-K) x)(y₀:Rooted l (P-Q) y)
    :Rooted l (stitch G F P-stitch H K Q) (x*(a*c)+b*(d*c)+b*(a*y)):= by
     have hl:= (stitch_root g x₀ hp|>.add (stitch_root he hk hp)).add (stitch_root h hk y₀)
     rw [coldF g hf hk hp,coldC g h hk hp,coldL h hk hp hq] at hl
     convert! hl using 1; abel
end Join
lemma Rooted.emptySpace [IsEmpty ι](l: Range X)(F:Field ι X)(h:0≤c) : Rooted l F c := ⟨h, fun i _=> isEmptyElim i⟩
end YM.Pulse
