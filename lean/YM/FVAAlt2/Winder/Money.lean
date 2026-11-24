import YM.RegulatorIR.Budget.Sums
import YM.RegulatorIR.Tape.Converge
/-!
# Anchored and row-norm convergence tools for genuine periodic Bulk Fk

Here take ℓ¹ cost, fixed horizon and history. Uniform refers to anchors on tensor coefficient space or row of a layer (no volume powers). No demand for uniform Laplace remainder! Period padding will give strong convergence on centered coordinates; errors through curved histories after coefficient extraction via schedules. tape up from YM.RegulatorIR.Tape is another branch; this folder uses its (checked-closure) ENNReal dominated convergence & L¹ shift proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind
open Set Filter Function
open scoped ENNReal NNReal BigOperators Classical Topology
variable {X Y Z W : Type} {l:Filter W}{v u:X→ℝ}{g h:W→X→ℝ}{C D:ℝ≥0∞}
abbrev cost (T:X→ℝ) := quota T 1
structure Earn (l:Filter W)(C:ℝ≥0∞)(v:X→ℝ)(g:W→X→ℝ): Prop where
   high : C≠⊤
   roof : cost v ≤ C
   terms w : cost (g w) ≤ C
   up : Tendsto (fun i=>cost (g i-v)) l (𝓝 0)

lemma step_through (a:X)(v:X→ℝ) : ‖v a‖ₑ ≤ cost v:= (mul_one _).symm.trans_le (term_le v 1 a)
lemma up_prod (T:X×Y→ℝ) : cost T=∑' i,cost (fun j=> T (i,j)):= quota_prod (Function.curry T) (fun _ _=>1)
lemma amassed (T:X→ℝ) (h:cost T ≠ ⊤):Summable T:= quota_summable (fun _=>le_rfl) h
lemma individually (v:X→ℝ) (g:X ↪ Y): cost (Stalk.collect (⇑g) v)=cost v :=by
 have hs(i:X) : Stalk.collect (⇑g) v (g i)=v i:= by
    unfold Stalk.collect; rw [tsum_eq_single ⟨i,rfl⟩]; intro j hj; exact (hj (Subtype.ext (g.injective j.property ))).elim
 unfold cost; rw [quota_base, quota_base, ← g.injective.tsum_eq]; simp_rw [hs];
 intro y hy; by_contra hw; haveI : IsEmpty (Stalk (⇑g) y):=⟨fun j=> hw ⟨ j.val,j.property⟩⟩; apply hy; change ‖Stalk.collect (⇑g) v y‖ₑ=0; unfold Stalk.collect; rw [tsum_empty,enorm_zero]
lemma Earn.full (h:Earn l C v g): cost v<⊤:= h.roof.trans_lt (lt_top_iff_ne_top.mpr h.high)
lemma Earn.out (h:Earn l C v g)(w) : cost (g w)<⊤:= (h.terms w).trans_lt (lt_top_iff_ne_top.mpr h.high)
lemma Earn.scrub (m:Earn l C v g)(hp:C≤ D)(he:D≠⊤): Earn l D v g := ⟨he,m.roof.trans hp,fun w=>(m.terms w).trans hp,m.up⟩
lemma Earn.pays (m:Earn l C v g)(f:Y→X) (hf:Injective f): Earn l C (v∘f) (fun i=> g i∘f):= ⟨m.high,(quota_restrict f hf v 1).trans m.roof,fun i=>(quota_restrict f hf (g i) 1).trans (m.terms i),Tape.first_zero m.up (fun i=>quota_restrict f hf (g i-v) 1) ⟩
lemma Earn.charges (h:Earn l C v g) (p:X→Y): Earn l C (Stalk.collect p v) (fun i => Stalk.collect p (g i)) := by
 refine ⟨ h.high, ( Stalk.quota_collect p v 1 ).trans h.roof, fun i=> ( Stalk.quota_collect p (g i) 1 ).trans (h.terms i), Tape.first_zero h.up fun i=> ?_ ⟩
 change cost _ ≤ cost _
 rw [show Stalk.collect p (g i) - Stalk.collect p v=Stalk.collect p (g i-v) from ?_ ]; exact Stalk.quota_collect p (g i-v) 1
 ext1 z; let E: Stalk p z ↪ X := Function.Embedding.subtype _
 exact Eq.symm ((amassed (g i) (h.out i).ne|>.comp_injective E.injective ).tsum_sub (amassed v h.full.ne |>.comp_injective E.injective))
lemma Earn.sumSecond {v:X×Y→ℝ}{g:W→X×Y→ℝ}(h:Earn l C v g): Earn l C (fun x=> ∑'y,v (x,y)) (fun w x=> ∑'y,g w (x,y)):= by
 let E(x:X) : Y≃ Stalk (Prod.fst:X×Y→X) x:= {
    toFun:=fun i=>⟨(x,i),rfl⟩, invFun:= fun z=> z.val.2, left_inv:= fun _=> rfl, right_inv:= fun i=> (Subtype.ext (Prod.ext i.property.symm rfl)) }
 have he(u:X×Y→ℝ) : (fun x=>∑'y,u (x,y))=Stalk.collect Prod.fst u:=funext fun x=> (E x).tsum_eq ( u ∘ Subtype.val )
 rw [he,show (fun w x=> ∑'y,g w (x,y))=(fun w=> Stalk.collect Prod.fst (g w)) from funext (fun i=>he _)]; exact h.charges _
lemma Earn.add (m:Earn l C v g)(n:Earn l D u h) : Earn l (C+D) (v+u) (fun i=> g i+h i) :=by
 refine ⟨ ENNReal.add_ne_top.mpr ⟨m.high,n.high⟩,(quota_add ..).trans (add_le_add m.roof n.roof),fun i=>(quota_add ..).trans (add_le_add (m.terms i) (n.terms i)), Tape.first_zero (by simpa only [add_zero] using m.up.add n.up ) fun i=>?_ ⟩
 rw [show g i+h i -(v+u)=g i-v+(h i-u) from by abel]; exact quota_add ..
lemma Earn.scale(m:Earn l C v g)(t:ℝ): Earn l (‖t‖ₑ*C) (t • v) (fun i=> t • g i) :=by
 have hx (y : X→ℝ) : cost (t • y)= ‖t‖ₑ * cost y:= quota_times y 1 t
 refine ⟨ ENNReal.mul_ne_top (by finiteness) m.high,(hx v).trans_le (mul_le_mul_right m.roof _),fun i=>(hx _).trans_le (mul_le_mul_right (m.terms i) _),?_⟩
 simp_rw [ ← smul_sub,hx]; simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a:= ‖t‖ₑ) m.up (Or.inr (by finiteness))
lemma Earn.const (hv: cost v≤ C)(h:C≠⊤): Earn l C v (fun _ => v) := ⟨h,hv,fun _=>hv,by simp_rw [sub_self,cost,quota_zero]; exact tendsto_const_nhds⟩
lemma Earn.free : Earn l 0 (0:X→ℝ) (fun _=>0):= Earn.const (quota_zero _).le ENNReal.zero_ne_top
lemma Earn.point (m:Earn l C v g)(i:X):Tendsto (fun w=>g w i) l (𝓝 (v i)) := tendsto_iff_enorm_sub_tendsto_zero.mpr (Tape.first_zero m.up fun _=> step_through i _)

lemma append_cost (u:X→ℝ)(v:X→Y→ℝ)(h: ∀ i,cost (v i)≤ C): cost (fun z:X×Y=> u z.1*v z.1 z.2) ≤ cost u*C:= by
 rw [up_prod]; change (∑' i,cost fun j=> u i*v i j)≤ _; unfold cost; simp_rw [quota_times]; rw [quota_base (_:X→ℝ),← ENNReal.tsum_mul_right]; exact ENNReal.tsum_le_tsum fun i=> mul_le_mul_right (h i) _
lemma Earn.link (n:Earn l D v g) {t:X→Y→ℝ} {a: W→X→Y→ℝ}(hx:∀ i:X,Earn l C (t i) ( fun w=>a w i ))(h:C≠⊤): Earn l (D*C) (fun z:X×Y=> v z.1*t z.1 z.2) (fun i z=>g i z.1*a i z.1 z.2):= by
 refine ⟨ENNReal.mul_ne_top n.high h,(append_cost v t (fun i=>(hx i).roof)).trans (mul_le_mul_left n.roof _),fun i=>(append_cost (g i) (a i) (fun x=>(hx x).terms i)).trans (mul_le_mul_left (n.terms i) _),?_ ⟩
 let e w x := ‖v x‖ₑ * cost (a w x-t x)
 have he : Tendsto (fun w=>∑'x,e w x) l (𝓝 0):= by
    apply Tape.dominated (f:=fun x=> ‖v x‖ₑ *( C+C ))
    · intro x; simpa only [e,mul_zero] using ENNReal.Tendsto.const_mul (a:= ‖v x‖ₑ) (hx x).up (Or.inr (by finiteness))
    · exact fun i x=> mul_le_mul_right ((quota_sub ..).trans (add_le_add ( (hx x).terms i ) (hx x).roof)) _
    rw [ENNReal.tsum_mul_right,←quota_base]; exact ENNReal.mul_lt_top n.full (by finiteness)
 refine Tape.first_zero (by simpa only [add_zero,zero_mul] using (Tape.multiplyZero C (lt_top_iff_ne_top.mpr h) (y:= fun _=> C) n.up tendsto_const_nhds).add he) fun i=>?_
 let u(z:X×Y):=(g i z.1-v z.1)*a i z.1 z.2; let b(z:X×Y):=v z.1*(a i z.1 z.2-t z.1 z.2)
 change cost ((fun z:X×Y=> g i z.1*a i z.1 z.2)-_ )≤_
 rw [show (fun z:X×Y=> g i z.1*a i z.1 z.2) - (fun z:X×Y=>v z.1*t z.1 z.2)= u+b from funext fun j=> by simp only [u,b,Pi.add_apply,Pi.sub_apply]; ring]
 refine (quota_add ..).trans (add_le_add ( append_cost (g i-v) (a i) (fun x=> (hx x).terms i) ) ?_); rw [ show quota b 1=_ from up_prod b ]; exact le_of_eq (tsum_congr fun j=> quota_times (a i j-t j) 1 (v j) )
lemma noone (v: Unit→ℝ): cost v= ‖v ()‖ₑ:=by simp [cost]
lemma Earn.propel {a_ :W→X→ℝ} (n:Earn l D v g)(h:C≠⊤)(hx:∀ i, Tendsto (fun w => a_ w i) l (𝓝 (u i))) (he:∀ i, ‖u i‖ₑ≤ C)(hp:∀ w i,‖a_ w i‖ₑ ≤ C) : Earn l (D*C) (v*u) (fun w=> g w * a_ w):=by
 let f(i:X)(_ : Unit):=u i; let y(w:W)(i:X)(_ : Unit):= a_ w i
 have he i : Earn l C (f i) (fun w=>y w i) := by refine ⟨h,(noone _).le.trans (he _),fun w=>(noone _).le.trans (hp w _),?_ ⟩; simp_rw [noone]; exact tendsto_iff_enorm_sub_tendsto_zero.mp (hx i)
 exact (n.link (t:=f) (a:=y) he h).pays (fun i=>(i, ())) (fun i j he=>congr_arg Prod.fst he)
end YM.RegulatorIR.Budget.FVAAlt2.Wind
