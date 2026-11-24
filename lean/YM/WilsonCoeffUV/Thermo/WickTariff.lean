import YM.WilsonCoeffUV.Thermo.Slots
/-!
# Prices through Polchinski brackets.
Budget autodecrement across time at fixed output degree, not steps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r l j:ℕ} {A B D C X Y σ η : ℝ}
variable {d:Distance U}

lemma comps_head {x : Fin r→U}(i:U) (f:U→V): Fin.cons (f i) (f ∘ x)= f ∘ Fin.cons i x:= funext fun j=> Fin.cases (by simp) (fun _=>by simp) j

lemma brim_cup (x:dock U α r)(y:dock U α 2): course d x y ≤ soar d (Fin.cons (y 1) (Fin.cons (y 0) x)):=by
  set a : Fin (r+2) → U × α := Fin.cons (y 1) (Fin.cons (y 0) x); set b :=Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)
  have he i: ∃ j,b i=(a j).1:= by
    cases i with
    | inl i=> refine ⟨i.succ.succ,?_⟩; simp [b,a]
    | inr i=> fin_cases i
              · exact ⟨Fin.succ 0,rfl⟩
              exact ⟨0,rfl⟩
  refine league_le d b fun i j=>?_; obtain ⟨u,hu⟩:= he i; obtain ⟨v,hv⟩:= he j
  rw [hu,hv]; exact leg_le d (Prod.fst ∘ a) u v
lemma branch_cup (x:dock U α (r+k))(y:dock U α 2):
    course d x y ≤ soar d (Fin.cons (y 0) (x ∘ Fin.castAdd k)) + d.gap (y 0).1 (y 1).1 + soar d (Fin.cons (y 1) (x ∘ Fin.natAdd r)):=by
  set a : Fin (r+1) → U × α :=Fin.cons (y 0) (x ∘ Fin.castAdd k); set b : Fin (k+1) → U × α :=Fin.cons (y 1) (x ∘ Fin.natAdd r); set c:= Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)
  have hl i: (∃ j,(a j).1=c i) ∨ ∃ j,(b j).1=c i:=by
    cases i with
    | inr i=> fin_cases i
              · exact Or.inl ⟨0,rfl⟩
              exact Or.inr ⟨0,rfl⟩
    | inl i=>
      refine Fin.addCases (fun j=> Or.inl ⟨j.succ,?_⟩) (fun j=> Or.inr ⟨j.succ,?_⟩) i <;> simp [a,b,c]
  let m:= soar d a + d.gap (y 0).1 (y 1).1 + soar d b
  have hv i j : d.gap (a i).1 (b j).1≤m := (d.tri (a i).1 (a 0).1 (b j).1).trans ((Nat.add_le_add (leg_le d (Prod.fst ∘ a) i 0) ((d.tri (a 0).1 (b 0).1 (b j).1).trans (Nat.add_le_add_left (leg_le d (Prod.fst ∘ b) 0 j) (d.gap (a 0).1 (b 0).1)))).trans_eq (Nat.add_assoc ..).symm)
  refine league_le d c fun i j=>?_; rcases hl i with ⟨u,hu⟩|⟨u,hu⟩<;>rcases hl j with ⟨v,hv'⟩|⟨v,hv'⟩<;> rw [←hu,←hv']
  · exact (leg_le d (Prod.fst ∘ a) _ _).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  · exact hv ..
  · rw [d.swap]; exact hv ..
  exact (leg_le d (Prod.fst ∘ b) _ _).trans (Nat.le_add_left ..)
lemma course_roll (d:Distance U)(x:dock U α r)(y:dock U α k) (v:Equiv.Perm (Fin r)): course d (x ∘ v) y=course d x y:=by
  let T:= v.sumCongr (Equiv.refl (Fin k)); let f:=Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)
  change league d _= league d f; rw [← league_equiv d f T]; congr 1; ext i; cases i <;>rfl

section
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
-- integrand single order. conventional nsmul.

def rain (G:ropes U α α)(P:Gen V (U×α))(r:ℕ):canal U α α V 2 r:= fun x y=> (G (y 0) (y 1)/2) • sever (y 0) (sever (y 1) P) r x
lemma rain_spell (G:ropes U α α)(P:Gen V (U×α))(r:ℕ)(x y) : rain G P r x y= ((1/2:ℝ) * G (y 0) (y 1)*(r+1:ℕ)*(r+2:ℕ)) • P (r+2) (Fin.cons (y 1) (Fin.cons (y 0) x)):=by rw [rain,sever,sever,Pi.smul_apply,prune,Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (R:=ℝ),← Nat.cast_smul_eq_nsmul (R:=ℝ),smul_smul,smul_smul]; congr 2; ring
lemma rain_bill {G:ropes U α α}{P:Gen V (U×α)}{r:ℕ}(h:dragCup d σ B G)(e:Amber d σ A (P (r+2)))(he:0≤σ): pairCup d σ (B*A*((1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ))) (rain G P r):=by
  have hb:=h.1; have ha:=e.1
  refine ⟨by positivity,fun x y=>?_⟩
  have hf : |G (y 0) (y 1)| ≤ B := (h.2 ..).trans (by
     conv_rhs=> rw [show B=B*1 from (mul_one _).symm]
     exact mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he) (by positivity))) hb)
  let m:=course d x y
  rw [rain_spell,norm_smul,Real.norm_eq_abs]; have hx:= brim_cup (d:=d) x y
  simp_rw [abs_mul]; push_cast; simp only [abs_one,abs_div,abs_of_nonneg (by positivity : 0≤ (2:ℝ)), abs_of_nonneg (by positivity : 0≤(r:ℝ)+1), abs_of_nonneg (by positivity : 0≤(r:ℝ)+2)]
  have hw : ‖P _ (Fin.cons (y 1) (Fin.cons (y 0) x))‖ ≤ A*Real.exp (-σ*m):= (e.2 _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hx) (by linarith))) ha)
  calc
    _ ≤ 1/2*B*(r+1)*(r+2)*(A*Real.exp (-σ*m)) := mul_le_mul (by gcongr) hw (norm_nonneg _) (by positivity)
    _ = _ := by unfold m; ring

-- shuffle contraction before normal division.
def rill (G:ropes U α α)(P:Gen ℝ (U×α))(Q:Gen V (U×α))(r i j:ℕ) : canal U α α V 2 r:= fun x y=> (G (y 0) (y 1)/2) • interweave (sever (y 0) P i) (sever (y 1) Q j) r x
lemma rill_spell (G:ropes U α α)(P:Gen ℝ (U×α))(Q:Gen V (U×α))(i j:ℕ)(x y): rill G P Q (i+j) i j x y= ((1/2:ℝ)*G (y 0) (y 1)*(i+1:ℕ)*(j+1:ℕ)* P (i+1) (Fin.cons (y 0) (x ∘ Fin.castAdd j))) • Q (j+1) (Fin.cons (y 1) (x ∘ Fin.natAdd i)):=by
  rw [rill, interweave,dif_pos rfl,sever,sever,Pi.smul_apply,Pi.smul_apply,← Nat.cast_smul_eq_nsmul (R:=ℝ),← Nat.cast_smul_eq_nsmul (R:=ℝ), smul_smul,smul_smul,smul_eq_mul,prune]; congr 1; simp; ring
lemma rill_bill {G:ropes U α α}{P:Gen ℝ (U×α)}{Q:Gen V (U×α)} {i j k:ℕ}(h:dragCup d σ B G)(e:Amber d σ A (P (i+1)))(t:Amber d σ C (Q (j+1)))(he:0≤σ)(hv:i+j=k): pairCup d σ (((1/2:ℝ)*(i+1:ℕ)*(j+1:ℕ))*B*A*C) (rill G P Q k i j):=by
  subst k; have hb:= h.1; have ha:=e.1; have hc:=t.1
  refine ⟨by positivity,fun x y=>?_⟩
  let a : Fin (i+1) → U × α :=Fin.cons (y 0) (x ∘ Fin.castAdd j); let b : Fin (j+1) → U × α :=Fin.cons (y 1) (x ∘ Fin.natAdd i);
  let p:=soar d a; let q:= d.gap (y 0).1 (y 1).1; let f:=soar d b
  have hy : course d x y≤p+q+f:= branch_cup x y
  have hz : |P _ a| ≤ A*Real.exp (-σ*p):= e.2 _
  rw [rill_spell, norm_smul, Real.norm_eq_abs]; simp_rw [abs_mul]; push_cast; simp only [abs_div,abs_one,abs_of_nonneg (by positivity : 0≤ (2:ℝ)),abs_of_nonneg (by positivity : 0≤(i:ℝ)+1),abs_of_nonneg (by positivity : 0≤(j:ℝ)+1)];
  have hH : |G (y 0) (y 1)|≤ B*Real.exp (-σ*q) :=h.2 _ _
  calc
    _ ≤ ((1/2:ℝ)*(B*Real.exp (-σ*q))*(i+1)*(j+1)*(A*Real.exp (-σ*p)))*(C*Real.exp (-σ*f)):=
       mul_le_mul (mul_le_mul (by gcongr) hz (abs_nonneg _) (by positivity)) (t.2 b) (norm_nonneg _) (by positivity)
    _ = (1/2*(i+1)*(j+1)*B*A*C)*Real.exp (-σ*(p+q+f : ℕ)) := by rw [Nat.cast_add,Nat.cast_add,mul_add (-σ),mul_add (-σ), Real.exp_add,Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hy) (by linarith))) (by positivity)

def swivel (P:canal U α α V 2 r): canal U α α V 2 r:= (Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹ • ∑ v :Equiv.Perm (Fin r), fun x y=>P (x ∘ v) y
lemma swivel_cup {P:canal U α α V 2 r}(e:pairCup d σ A P): pairCup d σ A (swivel P):= by
  have ht (v: Equiv.Perm (Fin r)) : pairCup d σ A (fun x y=>P (x ∘ v) y) := ⟨e.1,fun x y=>by rw [← course_roll d x y v]; exact e.2 ..⟩
  let C:= (Fintype.card (Equiv.Perm (Fin r)):ℝ); have hc:0<C:= by unfold C; positivity
  have hw := (pairCup.sum (s:=Finset.univ) (fun i _=>ht i)).smul C⁻¹
  rw [abs_of_pos (by positivity),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,show ((Fintype.card (Equiv.Perm (Fin r)) : ℕ) : ℝ)=C from rfl, inv_mul_cancel_left₀ hc.ne'] at hw; exact hw

lemma swivel_gap {F Q:canal U α α V 2 r} (h:pairCup d σ A (F-Q)): pairCup d σ A (swivel F-swivel Q):= by
  rw [show swivel F-swivel Q=swivel (F-Q) from ?_]; exact swivel_cup h
  funext x y; simp only [swivel,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply, Finset.sum_sub_distrib,smul_sub]

lemma rain_gap {G H: ropes U α α}{P Q:Gen V (U×α)} {r:ℕ}(h:dragCup d σ B G)(ht:dragCup d σ D (G-H))(e:Amber d σ C (P (r+2)-Q (r+2)))(hx:Amber d σ A (Q (r+2)))(he:0≤σ):
    pairCup d σ (B*C*((1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ))+D*A*((1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ))) (rain G P r-rain H Q r):=by
  rw [show rain G P r-rain H Q r=rain G (P-Q) r+ rain (G-H) Q r from ?_]; exact (rain_bill h (P:=P-Q) e he).add (rain_bill ht hx he)
  funext x y; simp only [rain_spell, Pi.sub_apply,Pi.add_apply, Matrix.sub_apply,mul_sub,sub_mul,smul_sub,sub_smul]; abel

lemma rill_gap {G H:ropes U α α}{P P':Gen ℝ (U×α)}{Q Q':Gen V (U×α)}{i j k:ℕ}(h:dragCup d σ B H)(ht:dragCup d σ D (G-H))(e:Amber d σ A (P (i+1)))(t:Amber d σ C (Q (j+1)))(v:Amber d σ X (Q (j+1)-Q' (j+1)))(hx:Amber d σ A (P' (i+1)))(g:Amber d σ Y (P (i+1)-P' (i+1)))(he:0≤σ)(hv:i+j=k):
     let Z :ℝ:=(1/2:ℝ)*(i+1:ℕ)*(j+1:ℕ); pairCup d σ (Z*D*A*C+ Z*B*A*X + Z*B*Y*C) (rill G P Q k i j - rill H P' Q' k i j):=by
  intro Z; subst k; rw [show rill _ _ _ _ _ _-_=rill (G-H) P Q (i+j) i j + rill H P' (Q-Q') (i+j) i j + rill H (P-P') Q (i+j) i j from ?_]
  exact ((rill_bill ht e t he rfl).add (rill_bill h hx (Q:=Q-Q') v he rfl)).add (rill_bill h (P:=P-P') g t he rfl)
  funext x y; simp only [rill_spell, Pi.sub_apply,Pi.add_apply, Matrix.sub_apply,mul_sub,sub_mul,smul_sub,sub_smul]; abel
end
end YM.WilsonCoeffUV.Bank
