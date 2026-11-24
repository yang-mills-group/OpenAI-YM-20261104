import YM.FVA2.Wick.IBP

/-! # Partial evaluation of the finite Wick bill

Retains all bosonic legs and eliminates the ghosts. The RG/scale conditional
denominator has a separate construction. This normalization cancels the
determinant constants in the `Endμ` identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick.Fermion
open Function Set Finset Matrix
open MS MS.Koszul MS.Plane MS.Cylinder MS.Book MS.Orbit MS.Orbit.Cog MS.Swirl
open scoped BigOperators Topology ContDiff Matrix
variable {A J : Type} [FA:Fintype A] [DA:DecidableEq A] [FJ:Fintype J] [DecidableEq J]
local notation "c" => sector (A:=A) (J:=J)
local notation "T" => Index A J
local notation "κ" => ((1/2):ℂ)
local notation "Mx" => Matrix T T ℂ
local infixl:70 " ⋆ " => product c

def odd (A J : Type)[DecidableEq J] := ((1/2):ℂ) • antiBlock A J
/-- Grains; b must be symmetric when used in View. -/
def bev (Q : Matrix A A ℂ)(J : Type) : Matrix (Index A J) (Index A J) ℂ := ((1/2):ℂ) • fromBlocks Q 0 0 0
local notation "G" => (odd A J)
local notation "P" => cut A J

def Wg (A J : Type) [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J] : Op (Index A J) ℂ:= (cut A J).comp (Shot (odd A J))
local notation "U" => Wg A J
variable {F H : Raw (Index A J) ℂ} {n : ℕ}

omit [Fintype A] [DecidableEq A] [Fintype J]
lemma odd_c (x y:T) : Chill G x y = antiBlock A J x y := by unfold odd Chill; rw [Matrix.smul_apply, smul_eq_mul]; ring
lemma clear : Clear c G := by
  rintro (i|i|i) (j|j|j) he <;> first | rfl | ( simp [odd,antiBlock] at he )
lemma sym : Cog.Sym c G := by
  rintro (i|i|i) (j|j|j) <;> simp [odd,antiBlock, omega, Matrix.one_apply, sector,eq_comm]
  all_goals split_ifs <;> simp
lemma Shut (x y:T)(h : G x y≠0) : c x=true ∧ c y=true := by
  have he:= clear x y h; rw [← he]; suffices ht:c x=true from ⟨ht,ht⟩; rcases x with x|x; rcases y with y|y <;> simp [odd,antiBlock] at h; rfl
variable (b : Matrix A A ℂ)
local notation "B" => bev b J
local notation "L" => (κ • totalCov b J)
omit [DecidableEq J] in
lemma clear_b : Clear c B := by
  rintro (i|i) (j|j) he <;> first | rfl | ( simp [bev] at he )
omit [DecidableEq J] in
lemma sym_b (h : b.IsSymm) : Cog.Sym c B := by
  rintro (i|i) (j|j) <;> first | (solve | simp [bev]) | skip
  change κ * b i j = 1 * (κ * b j i); rw [h.apply,one_mul] -- orientation?
omit [DecidableEq J] in
lemma shut_b (x y:T)(h : B x y≠0) : c x=false ∧ c y=false := by
  have he:= clear_b b x y h; rw [← he]; suffices ht:c x=false from ⟨ht,ht⟩; rcases x with x|x; · rfl
  rcases y with y|y <;> simp [bev] at h
lemma total_loc (x y:T) : L x y=B x y+G x y:= by
  rcases x with x|x <;> rcases y with y|y <;> simp [totalCov,bev,odd,antiBlock]
lemma total_sym (h : b.IsSymm) : Cog.Sym c L := by
  intro x y; rw [total_loc,total_loc _ y x, mul_add,sym x y,sym_b b h x y]
lemma total_c : Clear c L := by
  intro x y h; by_contra he; apply h
  rw [total_loc,show B x y=0 from Classical.byContradiction (fun h=> he (clear_b b x y h)),
    show G x y=0 from Classical.byContradiction (fun h=> he (clear x y h)),add_zero]

include FA FJ
lemma lap_factors (h : F∈ Alone c)(H:Raw T ℂ) : frame G (F ⋆ H) = F ⋆ (frame G H) := by
  rw [fpΩ,fpΩ]; simp only [map_sum, map_smul]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _ => ?_
  by_cases he:G i j=0; · simp only [he,zero_smul]
  obtain ⟨hi,hj⟩:= Shut i j he
  have hx (i:T)(hi:c i=true)(v:Raw T ℂ) : D i (F ⋆ v) = F ⋆ D i v := by
    rw [D_product, alone_D h hi,map_zero,LinearMap.zero_apply, zero_add,(alone_pure h).signs, cross_false',one_smul]
  rw [diffPair_apply,diffPair_apply,hx i hi,hx j hj]
lemma tep_factors (h : F∈ Alone c)(H:Raw T ℂ) (n:ℕ): tep G n (F ⋆ H) = F ⋆ (tep G n H) := by
  induction n with| zero=> rw [rise]; rfl| succ n ih=> rw [teen,teen, ih, lap_factors h, map_smul]
lemma Shot_factors (h : F∈ Alone c)(hF:F∈ Mini T)(hH:H∈ Mini T) : Shot G (F ⋆ H) = F ⋆ (Shot G H) := by
  obtain ⟨m,hm⟩ := hH; obtain ⟨k,hk⟩:=hF
  let l:= k+m; have H1 : Limit H l := hm.up (by unfold l; omega); have H2 : Limit (F ⋆ H) l := by unfold l; rw [Nat.cast_add]; exact hk.pair hm
  rw [dawn _ H1,dawn _ H2]; simp only [effect,LinearMap.sum_apply,tep_factors h, map_sum]
lemma Shot_coin (z:ℂ) : Shot G (coin (A:=T) z)=coin z:= by rw [dawn _ (coinN z)]; simp [effect,rise]
include DA
lemma Wg_factors (h : F∈Alone c)(hF:F∈ Mini T)(hH:H∈ Mini T): U (F ⋆ H) = F ⋆ U H:= by
  unfold Wg; rw [LinearMap.comp_apply,LinearMap.comp_apply, Shot_factors h hF hH, cut_prod, alone_cut h]
lemma Wg_coin (z : ℂ): U (coin (A:=T) z)=coin z:= by
  unfold Wg; rw [LinearMap.comp_apply,Shot_coin,cut,pull_coin]
lemma Wg_alone (F:Raw T ℂ) : U F∈Alone c := cut_alone _
lemma Wg_sym (he : Symm c F)(h : F∈Mini T) : Symm c (U F) := by
  apply pull_symm cut_tie; obtain ⟨n,hn⟩ := h; rw [dawn _ hn]; unfold effect; rw [LinearMap.sum_apply]; exact Symm.sum _ fun i _ => te2 _ he
lemma Wg_cap (h : Limit F n) : Limit (U F) n := by
  apply pull_limit; rw [dawn _ h]; unfold effect; rw [LinearMap.sum_apply]; exact Limit.sum _ fun i _ => Limit.up (te2H _ h) (by omega)
lemma Wg_mini (h : F∈Mini T) : U F∈Mini T := by obtain ⟨n,hn⟩ := h; exact minH (Wg_cap hn)

lemma Wg_D {x:T}(hh:c x=false)(he:Symm c F)(h:F∈Mini T) : D x (U F)= U (D x F):= by
  unfold Wg; obtain ⟨k,hk⟩:= h; rw [LinearMap.comp_apply,LinearMap.comp_apply,
    dawn _ hk,dawn G ((hk.tip x).up (show (k:ℤ)-1 ≤ (k:ℤ) from by omega)), cutD]
  rw [hh, if_neg Bool.false_ne_true]; unfold effect; simp only [LinearMap.sum_apply,map_sum,té_D G clear he]

lemma Wg_odd_D (x:T)(hh:c x=true)(he:Symm c F)(h:F∈Mini T):
    U (atLetter x ⋆ F) = ∑ i, Chill G x i • U (D i F) := by
  obtain ⟨n,hn⟩:=h
  -- totalT in Mace, with one spare step cap
  change P (Shot G _) = _
  rw [dawn G (n:=n+1) (by push_cast; rw [add_comm _ 1]; exact (letterN x).pair hn),
    totalT x clear sym he, map_add, cut_prod, cut_letter x hh, map_zero, LinearMap.zero_apply,
    zero_add, trdΩ, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl; intro i _
  unfold Wg effect
  rw [LinearMap.comp_apply,dawn (n:=n) G (Limit.up (hn.tip i) (by omega)),effect]
  simp only [LinearMap.sum_apply,map_sum,té_D G clear he]

lemma total_w (hb:b.IsSymm)(hF:Symm c F)(hv:F∈Mini T) : View L F = View B (U F) := by
  apply view_unique c L (total_c b) (total_sym b hb) ((View B).comp (Wg A J)) _ _ F hF hv
  · intro x H hh h
    change View B (U (atLetter x ⋆ H)) = ∑ i, Chill L x i * View B (U (D i H))
    by_cases hx:c x=false
    · have he (i:T) : Chill L x i = Chill B x i := by
        unfold Chill; rw [total_loc,show G x i=0 from Classical.byContradiction (fun he=> Bool.false_ne_true (hx.symm.trans ((Shut x i he).1))),add_zero]
      simp_rw [he]
      rw [Wg_factors (alone_letter x hx) (minH (letterN x)) h,ibpV x (clear_b b) (sym_b b hb) (Wg_sym hh h) (Wg_mini h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h1:B x i=0; · simp [Chill, h1]
      rw [Wg_D (shut_b b x i h1).2 hh h]
    have he (i:T) : Chill L x i= Chill G x i := by unfold Chill; rw [total_loc,show B x i=0 from Classical.byContradiction (fun he=> hx (shut_b b x i he).1), zero_add]
    simp_rw [he]; rw [Wg_odd_D x (by simpa using hx) hh h, map_sum]
    exact Finset.sum_congr rfl fun _ _ => map_smul (View B) _ _
  intro z; rw [LinearMap.comp_apply, Wg_coin]; exact minView ..
end YM.FVA2.Wick.Fermion
