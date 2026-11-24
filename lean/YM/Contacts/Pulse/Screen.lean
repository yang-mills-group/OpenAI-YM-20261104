import YM.Contacts.Pulse.Laminar
import YM.MergeProof.BarCode
/-! Positive-arity kernels and their rolled images. These charges are actual
absolute series over cover positions. Does not assert convergence of formal loop sums.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Set Filter RG Push.AbsoluteSums MergeProof
open scoped Classical BigOperators Topology NNReal
variable {ι κ X Y A B C D Q : Type*}

-- compress charged series along a map
variable {f:A→ℝ}{g:B→ℝ}{w:B→ℝ}{a:ℝ}
def Scroll (p:A→ B) (f:A→ℝ) (g:B→ℝ): Prop:= ∀ b,g b=cram p f b
namespace Scroll
variable {p:A→B}(h: Scroll p f g)
theorem comp (h:Scroll p f g){q:B→ C}{t:C→ℝ} (H:Scroll q g t) (hf:Summable f): Scroll (q∘p) f t:=by
  intro i; simp_rw [H i,expand_eq];
  let x (z:A):=if (q∘p) z=i then f z else 0
  have hx:Summable x:= hf.indicator (s:={z|(q∘p) z=i})
  rw [←(MergeProof.heavy p hx).tsum_eq]; refine tsum_congr (fun b=>?_)
  unfold cram; by_cases hz:q b=i
  · rw [if_pos hz,h b]; apply tsum_congr; rintro ⟨j,hj⟩; exact (if_pos (show (q ∘ p) j=i from (congr_arg q hj).trans hz)).symm
  rw [if_neg hz]; simp [x,fun (j:{j//p j=b})=> j.property,hz]
-- Fubini over π in a product with independently supplied rows
lemma chain (h:Scroll p f g){q:C→ D}{k:A→ C→ℝ}{t:B→D→ℝ} (H:∀ a, Scroll q (k a) (t (p a)))(hs:Summable (fun a:A× C=> f a.1*k a.1 a.2)): Scroll (Prod.map p q) (fun a:A× C=> f a.1*k a.1 a.2) (fun b=>g b.1 * t b.1 b.2) := by
  rintro ⟨x,y⟩
  rw [expand_eq]; let F:= (fun a:A× C=> f a.1*k a.1 a.2)
  let T : Set (A × C) := {a| Prod.map p q a=(x,y)}
  have hl:= hs.indicator (s:=T)
  change g x * t x y=∑' a:A× C,if Prod.map p q a=(x,y) then F a else 0
  rw [(show Summable (fun a:A× C=> if Prod.map p q a=(x,y) then F a else 0) from hl.congr fun i=> by simp [T,F,Set.indicator]).tsum_prod]
  rw [h, expand_eq, ← tsum_mul_right]; apply tsum_congr; intro x'
  by_cases he:p x'=x
  · rw [if_pos he,← he,H,expand_eq,← tsum_mul_left]; apply tsum_congr; intro y'; dsimp [F]; split <;> split <;> grind
  simp [he,F]
lemma direct (hf:Summable f)(_h:Scroll p f g)(i : B): Summable (fun x:{a// p a=i}=>f ↑x):= hf.comp_injective Subtype.val_injective
lemma cost (h:Scroll p f g)(hn:∀ i,0≤ w i)(hs:Summable f)(hf:SumBudget (fun x=> ‖f x‖*w (p x)) a) : SumBudget (fun x=> ‖g x‖*w x) a:= by
  let v x:=‖f x‖*w (p x); have hv:SumBudget (cram p v) a:= ⟨fun _=>tsum_nonneg fun i=> hf.1 _, (heavy _ hf.2.1).summable, (heavy _ hf.2.1).tsum_eq.trans_le hf.2.2⟩
  apply budget_mono hv (fun x=> mul_nonneg (norm_nonneg _) (hn _)); intro b; rw [h]; unfold cram
  apply le_trans (mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm ?_) (hn _))
  · rw [←tsum_mul_right]; apply le_of_eq; apply tsum_congr; intro x; simp only [v,x.property]
  exact (summable_abs_iff.mpr hs).comp_injective Subtype.val_injective
lemma summable (h:Scroll p f g)(hf:Summable f): Summable g:=(funext h) ▸ (heavy _ hf).summable
lemma add (h: Scroll p f g){f' g'}(H: Scroll p f' g')(hf:Summable f)(hg:Summable f') : Scroll p (f+f') (g+g'):= fun b=> by simp only [Pi.add_apply]; rw [h,H]; simp only [cram,Pi.add_apply]; rw [(h.direct hf b).tsum_add (H.direct hg b)]
lemma scale (h:Scroll p f g)(c:ℝ): Scroll p (c • f) (c • g):=fun b=> by simp only [Pi.smul_apply]; rw [h]; simp only [cram,Pi.smul_apply,smul_eq_mul,tsum_mul_left]
lemma empty (p:A→B): Scroll p (fun _=>0) (fun _=>0):= fun _=> by simp [cram]
lemma across (h:Scroll p f g) (e:C ≃ A) (w : D≃B){q:C→D} (he: ∀ c, w (q c)=p (e c)): Scroll q (f∘e) (g∘w):= by
  intro x; rw [Function.comp_apply,h,expand_eq, expand_eq, ← e.tsum_eq]; apply tsum_congr; intro y; simp only [←he,w.apply_eq_iff_eq,Function.comp_apply]
lemma fst_column  (t:A× C→ℝ): Scroll Prod.fst t (fun i=>∑' j,t (i,j)):= by
    intro i; let e:C ≃ {j:A×C// j.1=i}:= ⟨fun j=>⟨(i,j),rfl⟩,fun j=>j.1.2,fun _=>rfl,fun a=>Subtype.ext (Prod.ext a.property.symm rfl)⟩
    exact e.tsum_eq (fun j=>t ↑j)
lemma collapse_fst {q:C→D}{f:A×C→ℝ}{g:B×D→ℝ} (h:Scroll (Prod.map p q) f g)(hf: Summable f): Scroll p (fun i=> ∑' j,f (i,j)) (fun i=>∑' j,g (i,j)):= by
  intro i; dsimp only; rw [show (∑' j,g (i,j))=cram (p∘ Prod.fst) f i from h.comp (fst_column g) hf i]
  exact (comp (fst_column f) (fun i=> (rfl: (cram p (fun a=>∑' j, f (a,j))) i=_)) hf i).symm
end Scroll

section
variable (p : X→Y)
def roll (i:ι)(x:X)(u:Locked X i x): Locked Y i (p x):=⟨p ∘ u.val, by simp [u.property]⟩
def Shadow (F:Field ι X)(H:Field ι Y): Prop:= ∀ i x, Scroll (roll p i x) (fun u=>F u.val) (fun v=>H v.val)
def Lay (F:Field ι X)(i:ι)(x:X)(y:ι→Y) := ∑' p0:{u:Locked X i x//p ∘ u.val=y}, F (p0.val.val)
variable {p} {F:Field ι X} {H:Field ι Y}
lemma roll_cram {i:ι}{x:X} (p:X→Y)(v:Locked Y i (p x)) : cram (roll p i x) (fun u=>F u.val) v = Lay p F i x v.val := by
  let e:{u:Locked X i x// roll p i x u=v}≃{u:Locked X i x//p ∘ u.val=v.val}:= Equiv.subtypeEquivRight (fun z=> Subtype.ext_iff)
  exact e.tsum_eq (fun u=> F u.val.val)
lemma Shadow.rule (h:Shadow p F H)(u:ι→Y)(i:ι)(x:X)(hx:p x=u i): H u= Lay p F i x u:= (h i x ⟨u,hx.symm⟩).trans (roll_cram ..)
lemma Shadow.cost [Fintype ι]{l:Range X}{m: Range Y}(h:Shadow p F H)(hc:Rooted l F a)(hl : ∀ i:ι→X,m.bill (p ∘ i) ≤ l.bill i)(hp: Surjective p): Rooted m H a:= by
  refine ⟨hc.cash,fun i y=>?_⟩; obtain ⟨x,rfl⟩:= hp y; exact (h i x).cost (fun v : Locked Y i (p x)=> show 0≤m.bill v.val from (by positivity)) (hc.raw i x).2.1.of_norm (budget_mono (hc.row i x) (fun _=> by positivity) (fun _=> mul_le_mul_of_nonneg_left (hl _) (norm_nonneg _)))
lemma Shadow.empty (p:X→Y): Shadow (ι:=ι) p (fun _=>0) (fun _=>0) := fun _ _=> Scroll.empty _
lemma Shadow.add [Fintype ι] (h:Shadow p F H){F' H'}(H₀:Shadow p F' H'){l l':Range X}{b c:ℝ}(hf:Rooted l F b)(hg:Rooted l' F' c): Shadow p (F+F') (H+H'):= fun i a=> (h i a).add (H₀ i a) ((hf.raw ..).2.1.of_norm) ((hg.raw ..).2.1.of_norm)
lemma Shadow.scale (h:Shadow p F H)(c:ℝ) : Shadow p (c • F) (c • H):= fun i x=> (h i x).scale c

end
end YM.Pulse
