import YM.XSpace.Flares

/-!
# Fold chart image contribution to the perturbative vacuum
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Comets
open Function Set Lattice RG Wilson Source Source.Drops Next.Rank.Normal Contraction Chart2 Finsupp JetGauge Legs MvPolynomial Feynman Filter Outline Outline.Given
open Sail (reach)
open scoped Topology BigOperators
variable {G:Gauge} {R:Period} {S Z:Type*} [AddCommGroup S][One S]
abbrev flash := (⟨Equiv.refl Axis,fun _=>true⟩:Signed)
lemma backward (x: R.Sites) : affine flash 0 x= -x:=by rw [affine,add_zero]; rfl
lemma is_image (p:Face (Per R.side)): Face.send flash 0 p= R.reflectedFace p:=by
  apply Prod.ext
  · simp only [Face.send,Face.lower,atFace,backward (R:=R)]; simp [Step.rotate, posDir,Step.vec, Period.reflectedFace,sub_eq_add_neg]
  have he := p.2.property; apply Subtype.ext; simp [Face.send,flash,Period.reflectedFace,PlaqAxes.rotate,PlaqAxes.ordered,he.le]
lemma chart_legal (U:R.Bonds→ G.Color)(h:Legit R U)(p:Face (Per R.side)) : diagnostic p U=diagnostic (R.reflectedFace p) U:=by
  let L(t:ℝ):Links (Per R.side) G.El:=fun e=>G.lieExp (t • U e)
  have he (t:ℝ): L t = Lattice.pull flash 0 (L t):=by funext e; rw [Lattice.pull, backward (R:=R)]; change G.lieExp (t • U e)= (G.lieExp (t • U (R.reflect e)))⁻¹; rw [legit_reflect h e,smul_neg,Work.F03.exp_neg_color,inv_inv]
  have hφ e : Fits (fun t=> L t e) (native U e):= Fits.along_a _
  rw [← diagnostic_price p L _ hφ, ← diagnostic_price _ L _ hφ]; congr 1; funext t; nth_rw 1 [he t]; rw [Face.send_price _ _ _ _ _ G.price_inv (fun k g=> G.price_conj g k),is_image (R:=R)]
lemma chart_guide (T:R.Tree)(p:Face (Per R.side)): Lift T (V3 G p)=Lift T (V3 G (R.reflectedFace p)):= Taylor.from_real (axisB T G) _ _ (fun x=> by rw [show Taylor.evalAt _ x (Lift T _)=_ from woven_at ..,price_at]; change _=readAt T x _; rw [woven_at,price_at,chart_legal _ (legit_route T _)])

def witness (q:Face S)(g:Given G S)(z:Z→ Four S)(p:Music):= E g.grant (V3 G q * shroud g z p)
lemma reflection (q:Face (Per R.side))(z:Z → R.Sites)(p:Music (G:=G) (Z:=Z)): witness q (dawn G R) z p=witness (R.reflectedFace q) (dawn G R) z p:=by
  let h (r) : witness r (dawn G R) z p=E (moving R.standardTree (meet G R)) (Lift R.standardTree (V3 _ r*shroud (dawn G R) z p)):= (into_wide ..).symm
  rw [h,h (R.reflectedFace _),map_mul (Lift R.standardTree),map_mul (Lift R.standardTree),chart_guide]

lemma witness_quotation (q:PlaqAxes)(p:Music (Z:=Z) (G:=G)) : ∃ C:ℝ,0≤C ∧ ∀ R:Period,∀ o: Cover,Tall R o→∀ r:ℕ,∀ x: Z→Cover,(∀ i,reach (x i-o) ≤r)→∀ y:Cover,reach (y-o)≤r→
    ‖witness (wrap R.side y,q) (dawn G R) (wrap R.side ∘ x) p - witness (y,q) (dusk G) x p‖ ≤ C*budget R r:=by
  let v:= V3 G ((0:Cover),q); let A (i:Bone G ℤ): (Unit ⊕ Z) × Bone G ℤ:= (.inl (),i); let B (i:Z×Bone G ℤ): (Unit ⊕ Z) × Bone G ℤ:=(.inr i.1,i.2)
  let L:Shadow (G:=G) (Z:=Unit ⊕ Z):= rename A v*rename B (film p)
  obtain ⟨C,hC,H⟩ := (arc L).1
  refine ⟨C,hC,fun R o ho r x hx y hy=>?_⟩
  have he {S:Type} [AddCommGroup S][One S] (Z': Given G S)(w : Unit⊕Z→ Four S) : motor Z' w L= V3 _ (w (.inl ()),q)*shroud Z' (w ∘ Sum.inr) p:= by
    have hh: motor Z' w (rename A v) = (Z'.points (w (.inl ()))).pull v:= motor_at ..
    have hv(u:Shadow): motor Z' w (rename B u)= motor Z' (w ∘ Sum.inr) u:=by unfold motor; rw [rename_rename]; rfl
    unfold L; rw [map_mul, hh, hv,operate]; unfold v; rw [Chart.v3]; simp
  set w:=Sum.elim (fun _=> y) x; specialize H R o ho r w (by rintro (a|a); exact hy; exact hx _); dsimp only at H; rw [he,he] at H; exact H

lemma full_cover (q:PlaqAxes)(p:Music (Z:=Z) (G:=G)) (z: Z→Cover): Summable (fun y:Cover=>witness (y,q) (dusk G) z p):=by
  obtain ⟨C,hC,H⟩:= toll_integrals (night G) p q; apply Summable.of_norm; exact summable_of_sum_le (c:= C *saving 0) (fun i=>norm_nonneg _) fun s=>H () 0 z s (fun x _ _=> Nat.zero_le _)
end YM.XSpace.Comets
