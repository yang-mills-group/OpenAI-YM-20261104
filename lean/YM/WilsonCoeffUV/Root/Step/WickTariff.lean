import YM.WilsonCoeffUV.Root.Step.Ledger
/-! # Uri taps, same-scale with single physical root birth. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open scoped Topology BigOperators
variable {n:Side}{U α β V ι E : Type*}{k r l j:ℕ} {A B C D X Y σ η : ℝ} {d:Distance U}{w:U}{p:Cover}

lemma tap_cup (x:dock U α r)(y:dock U α 2): brims d w x y ≤ tread d w (Fin.cons (y 1) (Fin.cons (y 0) x)):=by
    let A : dock U α (r+2) := Fin.cons (y 1) (Fin.cons (y 0) x); set b:= Sum.elim (stud w x) (Prod.fst ∘ y); let a:= stud w A
    have he i: ∃ j,b i= a j:=by
       cases i with
       | inl i=> refine Fin.cases ⟨0,rfl⟩ (fun j=>⟨Fin.succ (Fin.succ j.succ),by simp [b,stud,A,a]⟩) i
       | inr i=> fin_cases i
                 · exact ⟨Fin.succ (Fin.succ 0),rfl⟩
                 exact ⟨Fin.succ 0,rfl⟩
    refine league_le d b fun i j=>?_ ; obtain ⟨u,hu⟩:= he i; obtain ⟨v,hv⟩:= he j; rw [hu,hv]; exact leg_le d a _ _

lemma right_cup (x:dock U α (r+k))(y:dock U α 2):
    brims d w x y ≤ soar d (Fin.cons (y 0) (x ∘ Fin.castAdd k)) + d.gap (y 0).1 (y 1).1 + tread d w (Fin.cons (y 1) (x ∘ Fin.natAdd r)):=by
  set a : Fin (r+1) → U × α :=Fin.cons (y 0) (x ∘ Fin.castAdd k); set b : Fin (k+1) → U × α :=Fin.cons (y 1) (x ∘ Fin.natAdd r); set c:= Sum.elim (stud w x) (Prod.fst ∘ y); let B:=stud w b
  have hl i: (∃ j,(a j).1=c i) ∨ ∃ j,B j=c i:=by
    cases i with
    | inr i=> fin_cases i
              · exact Or.inl ⟨0,rfl⟩
              exact Or.inr ⟨Fin.succ 0,rfl⟩
    | inl i=>
      refine Fin.cases (Or.inr ⟨0,rfl⟩) (fun j=>?_) i
      refine Fin.addCases (fun u=> Or.inl ⟨u.succ,?_⟩) (fun u=> Or.inr ⟨Fin.succ u.succ,?_⟩) j <;> simp [a,c,B,b,stud]
  let m:= soar d a + d.gap (y 0).1 (y 1).1 + tread d w b
  have hv i j : d.gap (a i).1 (B j)≤m := (d.tri (a i).1 (a 0).1 (B j)).trans ((Nat.add_le_add (leg_le d (Prod.fst ∘ a) i 0) ((d.tri (a 0).1 (B (Fin.succ 0)) (B j)).trans (Nat.add_le_add_left (leg_le d B (Fin.succ 0) j) (d.gap (a 0).1 (B (Fin.succ 0)))))).trans_eq (Nat.add_assoc ..).symm)
  refine league_le d c fun i j=>?_; rcases hl i with ⟨u,hu⟩|⟨u,hu⟩<;>rcases hl j with ⟨v,hv'⟩|⟨v,hv'⟩<;> rw [←hu,←hv']
  · exact (leg_le d (Prod.fst ∘ a) _ _).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  · exact hv ..
  · rw [d.swap]; exact hv ..
  exact (leg_le d B _ _).trans (Nat.le_add_left ..)
lemma brims_roll (d:Distance U)(w:U)(x:dock U α r)(y:dock U α k) (v:Equiv.Perm (Fin r)): brims d w (x ∘ v) y=brims d w x y:=by
  let S: Equiv.Perm (Fin (r+1)) := ((finSuccEquiv r).trans (Equiv.optionCongr v)).trans (finSuccEquiv r).symm
  let T:= S.sumCongr (Equiv.refl (Fin k)); let f:=Sum.elim (stud w x) (Prod.fst ∘ y)
  change league d _= league d f; rw [← league_equiv d f T]; congr 1; ext i
  cases i with
  | inr i=>rfl
  | inl i=> refine Fin.cases (by simp [f, T,S,stud]) (fun j=> by simp [f,T,S,stud]) i

variable [NormedAddCommGroup V][NormedSpace ℝ V]
lemma solorain_bill {G:ropes U α α}{P:Gen V (U×α)}{r:ℕ}(h:dragCup d σ B G)(e:Cork d w σ A (P (r+2)))(he:0≤σ): Peb d w σ (B*A*((1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ))) (rain G P r):=by
  have hb:=h.1; have ha:=e.1
  refine ⟨by positivity,fun x y=>?_⟩
  have hf : |G (y 0) (y 1)| ≤ B := (h.2 ..).trans (by
     conv_rhs=> rw [show B=B*1 from (mul_one _).symm]
     exact mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he) (by positivity))) hb)
  let m:=brims d w x y
  rw [rain_spell,norm_smul,Real.norm_eq_abs]; have hx:= tap_cup (d:=d) (w:=w) x y
  simp_rw [abs_mul]; push_cast; simp only [abs_one,abs_div,abs_of_nonneg (by positivity : 0≤ (2:ℝ)), abs_of_nonneg (by positivity : 0≤(r:ℝ)+1), abs_of_nonneg (by positivity : 0≤(r:ℝ)+2)]
  have hw : ‖P _ (Fin.cons (y 1) (Fin.cons (y 0) x))‖ ≤ A*Real.exp (-σ*m):= (e.2 _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hx) (by linarith))) ha)
  calc
    _ ≤ 1/2*B*(r+1)*(r+2)*(A*Real.exp (-σ*m)) := mul_le_mul (by gcongr) hw (norm_nonneg _) (by positivity)
    _ = _ := by unfold m; ring

lemma solorill_bill {G:ropes U α α}{P:Gen ℝ (U×α)}{Q:Gen V (U×α)} {i j k:ℕ}(h:dragCup d σ B G)(e:Amber d σ A (P (i+1)))(t:Cork d w σ C (Q (j+1)))(he:0≤σ)(hv:i+j=k): Peb d w σ (((1/2:ℝ)*(i+1:ℕ)*(j+1:ℕ))*B*A*C) (rill G P Q k i j):=by
  subst k; have hb:= h.1; have ha:=e.1; have hc:=t.1
  refine ⟨by positivity,fun x y=>?_⟩
  let a : Fin (i+1) → U × α :=Fin.cons (y 0) (x ∘ Fin.castAdd j); let b : Fin (j+1) → U × α :=Fin.cons (y 1) (x ∘ Fin.natAdd i);
  let p:=soar d a; let q:= d.gap (y 0).1 (y 1).1; let f:=tread d w b
  have hy : brims d w x y≤p+q+f:= right_cup x y
  have hz : |P _ a| ≤ A*Real.exp (-σ*p):= e.2 _
  rw [rill_spell, norm_smul, Real.norm_eq_abs]; simp_rw [abs_mul]; push_cast; simp only [abs_div,abs_one,abs_of_nonneg (by positivity : 0≤ (2:ℝ)),abs_of_nonneg (by positivity : 0≤(i:ℝ)+1),abs_of_nonneg (by positivity : 0≤(j:ℝ)+1)];
  have hH : |G (y 0) (y 1)|≤ B*Real.exp (-σ*q) :=h.2 _ _
  calc
    _ ≤ ((1/2:ℝ)*(B*Real.exp (-σ*q))*(i+1)*(j+1)*(A*Real.exp (-σ*p)))*(C*Real.exp (-σ*f)):=
       mul_le_mul (mul_le_mul (by gcongr) hz (abs_nonneg _) (by positivity)) (t.2 b) (norm_nonneg _) (by positivity)
    _ = (1/2*(i+1)*(j+1)*B*A*C)*Real.exp (-σ*(p+q+f : ℕ)) := by rw [Nat.cast_add,Nat.cast_add,mul_add (-σ),mul_add (-σ), Real.exp_add,Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hy) (by linarith))) (by positivity)

lemma soloswivel_cup {P:canal U α α V 2 r}(e:Peb d w σ A P): Peb d w σ A (swivel P):= by
  have ht (v: Equiv.Perm (Fin r)) : Peb d w σ A (fun x y=>P (x ∘ v) y) := ⟨e.1,fun x y=>by rw [← brims_roll d w x y v]; exact e.2 ..⟩
  let C:= (Fintype.card (Equiv.Perm (Fin r)):ℝ); have hc:0<C:= by unfold C; positivity
  have hw := (Peb.sum (s:=Finset.univ) (fun i _=>ht i)).μ C⁻¹
  rw [abs_of_pos (by positivity),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,show ((Fintype.card (Equiv.Perm (Fin r)) : ℕ) : ℝ)=C from rfl, inv_mul_cancel_left₀ hc.ne'] at hw; exact hw

lemma soloswivel_gap {F Q:canal U α α V 2 r} (h:Peb d w σ A (F-Q)): Peb d w σ A (swivel F-swivel Q):= by
  rw [show swivel F-swivel Q=swivel (F-Q) from ?_]; exact soloswivel_cup h
  funext x y; simp only [swivel,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply, Finset.sum_sub_distrib,smul_sub]

lemma solorain_gap {G H: ropes U α α}{P Q:Gen V (U×α)} {r:ℕ}(h:dragCup d σ B G)(ht:dragCup d σ D (G-H))(e:Cork d w σ C (P (r+2)-Q (r+2)))(hx:Cork d w σ A (Q (r+2)))(he:0≤σ):
    Peb d w σ (B*C*((1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ))+D*A*((1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ))) (rain G P r-rain H Q r):=by
  rw [show rain G P r-rain H Q r=rain G (P-Q) r+ rain (G-H) Q r from ?_]; exact (solorain_bill h (P:=P-Q) e he).add (solorain_bill ht hx he)
  funext x y; simp only [rain_spell, Pi.sub_apply,Pi.add_apply, Matrix.sub_apply,mul_sub,sub_mul,smul_sub,sub_smul]; abel

lemma solorill_gap {G H:ropes U α α}{P P':Gen ℝ (U×α)}{Q Q':Gen V (U×α)}{i j k:ℕ}(h:dragCup d σ B H)(ht:dragCup d σ D (G-H))(e:Amber d σ A (P (i+1)))(t:Cork d w σ C (Q (j+1)))(v:Cork d w σ X (Q (j+1)-Q' (j+1)))(hx:Amber d σ A (P' (i+1)))(g:Amber d σ Y (P (i+1)-P' (i+1)))(he:0≤σ)(hv:i+j=k):
     let Z :ℝ:=(1/2:ℝ)*(i+1:ℕ)*(j+1:ℕ); Peb d w σ (Z*D*A*C+ Z*B*A*X + Z*B*Y*C) (rill G P Q k i j - rill H P' Q' k i j):=by
  intro Z; subst k; rw [show rill _ _ _ _ _ _-_=rill (G-H) P Q (i+j) i j + rill H P' (Q-Q') (i+j) i j + rill H (P-P') Q (i+j) i j from ?_]
  exact ((solorill_bill ht e t he rfl).add (solorill_bill h hx (Q:=Q-Q') v he rfl)).add (solorill_bill h (P:=P-P') g t he rfl)
  funext x y; simp only [rill_spell, Pi.sub_apply,Pi.add_apply, Matrix.sub_apply,mul_sub,sub_mul,smul_sub,sub_smul]; abel
end YM.WilsonCoeffUV.Soil
