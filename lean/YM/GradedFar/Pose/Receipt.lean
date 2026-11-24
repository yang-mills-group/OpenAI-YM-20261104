import YM.GradedFar.Pose.Price

/-!
# From pose cost to the untouched legs, on the compacta of the indicated stock
-/
namespace YM.FVA2.GradedFar.Pose
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m d : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=> gYM G
variable {F : Plans G d}
variable {K : Set (Points n)} (hK : IsCompact K) (hx : K ⊆ conf n)
    (u : ℝ → Normalize.Change G d) (t : ℝ → ℝ)
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

lemma coord_change {I : Type} {f : Filter I} {c : I → ℝ} {u : I → Normalize.Change G d} (x : Sec G d) (b : Toon G d)
    (hv : (fun i=> guide G d (u i))=O[f] c) : (fun i=>coord b (stand (u i) x)-coord b x)=O[f] c := by
  let L : MoveSpace G d→ₗ[ℝ] ℂ:={ toFun v:= coord b (((guide G d).symm v).val x), map_add' := by intro a m; rw [map_add]; exact map_add (coord b) _ _, map_smul':=by intro a m; rw [map_smul]; exact map_smul ((coord b).restrictScalars ℝ) _ _
  }
  obtain ⟨C,hC,hv⟩:= hv.exists_pos
  let L' : MoveSpace G d→L[ℝ] ℂ:= LinearMap.toContinuousLinearMap L
  apply IsBigO.of_bound (‖L'‖ * C); filter_upwards [hv.bound] with i hi
  rw [mul_assoc,stood,map_add,add_sub_cancel_left,show coord b ((u i).val x)= L' (guide G d (u i)) from
    (show _=coord b (((guide G d).symm (guide G d (u i))).val x) from by rw [LinearEquiv.symm_apply_apply])]
  exact le_trans (L'.le_opNorm _) (mul_le_mul_of_nonneg_left hi (norm_nonneg L'))

include H
lemma shrank (k j : ℕ) (h : k ≤ j) : (fun r=>g r^j)=O[τ] (fun r=>g r^k) := by
  cases H
  apply IsBigO.of_bound 1; filter_upwards [positive_g simple,(shrink simple).eventually_lt_const zero_lt_one] with r h0 he
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),one_mul]
  exact pow_le_pow_of_le_one h0.le he.le h
lemma fine (k : ℕ) : (fun r=>g r^k)=O[τ] (fun _=>(1:ℝ)) := by simpa only [pow_zero] using shrank N M H 0 k k.zero_le

/-- C5 t-provisional tends to zero. -/
lemma tainted (ht : Tendsto (fun r=>t r/g r) τ (𝓝 1)) : Tendsto t τ (𝓝 0) := by
  cases H
  have hf:= ht.mul (shrink simple)
  rw [one_mul] at hf; exact hf.congr' ((positive_g simple).mono fun r hr=> div_mul_cancel₀ _ hr.ne')

section price
variable {I : Type}
lemma terms_power (j k : ℕ) (h : k ≤ j) (ht : Tendsto (fun r=>t r/g r) τ (𝓝 1)) :
    Terms τ (fun r=>g r^k) (fun r (_ : I)=> (t r:ℂ)^j) := by
  apply Terms.blind
  apply IsBigO.trans _ (shrank N M H k j h); apply IsBigO.of_bound (2^j)
  filter_upwards [paid_reading simple _ ht,positive_g simple] with r hf hg
  rw [norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,Real.norm_of_nonneg hg.le]
  exact (pow_le_pow_left₀ (abs_nonneg _) hf.2.2.2 j).trans_eq (mul_pow ..)
lemma proper_power (j : ℕ) (ht : Tendsto (fun r=>t r/g r) τ (𝓝 1)) :
    Proper τ (fun r (_ : I)=> (t r:ℂ)^j) := (terms_power (I:=I) N M t H j j le_rfl ht).mono (fine N M H j)
end price

include hK hx
lemma proper_line (x : Tags G d n) (j : ℕ) :
    Proper τ (fun (_:ℝ) (z:↥K)=>coeff j (line N z.val x)) := by
  obtain ⟨C,h⟩:= hK.exists_bound_of_continuousOn (((birth N M H d).light _ j x).mono hx)
  simp_rw [line,coeff_mk]; exact Proper.bounded C (Eventually.of_forall fun r z=> h z.val z.property)
lemma crop_proper (x : Tags G d n) (q : ℕ) (ht : Tendsto (fun r=>t r/g r) τ (𝓝 1)) :
    Proper τ (fun r (z:↥K)=>crop q (t r) (line N z.val x)) := by
  simp only [crop_eq]; exact Terms.sum _ fun i _=> (proper_power N M t H i ht).left (proper_line N M hK hx H x i)

variable (X : Tags G d n)
private def tilt (n d : ℕ) (x : Points n) (t : ℝ) (q : ℕ) :=
  ∑ i∈Finset.range (q+1), (t:ℂ)^i • fxt (Bbook N d) x i
omit hK hx H in
private lemma tilted (x : Points n) (t : ℝ) (q : ℕ) :
    crop q t (line N x X)=tilt N n d x t q X := by
  unfold tilt line; simp only [crop_eq]; simp [ smul_eq_mul]
omit hK hx H in
lemma roman (q : ℕ) (x : Points n) (t : ℝ) :
   crop q t (line N x X)=∑ a:Choices G (fun _ : Fin n=>d), combo (d:=fun _=>d) X a * crop q t (line N x (basisInputs a)):= by
  simp_rw [tilted]; exact basis_spelling (tilt N n d x t q) X
omit hK hx in
lemma discrepancy (a:Choices G (fun _ : Fin n=>d)) (k : ℕ) (s : Finset (Fin n)) {I : Type}
    (H' : (fun r=>guide G d (u r))=O[τ] (fun r=>g r^k)) :
    Terms τ (fun r=>g r^k) (fun r (_:I)=> (∏ i∈s,coord (a i) (stand (u r) (X i)))-(∏ i∈s,coord (a i) (X i))) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,sub_self]; exact Terms.blind (isBigO_zero ..)
  | insert i s hi h =>
    let y (r : ℝ) := coord (a i) (stand (u r) (X i))
    let y' := coord (a i) (X i)
    have hp := Terms.blind (U:=I) (coord_change (X i) (a i) H')
    have he : Proper τ (fun r (_:I)=>y r) := by
      simpa only [sub_add_cancel,y] using (hp.mono (fine N M H k)).add (Proper.fixed (coord (a i) (X i)))
    simp only [Finset.prod_insert hi]
    exact (((Terms.right he h)).add (hp.left (Proper.fixed _))).eq (fun i j=> by unfold y; ring)

/-- Pose price (C5 cash) after pricing the matrix variation. -/
lemma pinned (q k : ℕ) (ht : Tendsto (fun r=>t r/g r) τ (𝓝 1))
    (H' : (fun r=> guide G d (u r))=O[τ] (fun r=>g r^k))
    (asks : Confirmed N F q k t u K X) :
    Terms τ (fun r=>g r^k) (fun r (x:↥K)=> F r n x.val X - crop q (t r) (line N x.val X)) := by
  have he (a : Choices G (fun _ : Fin n=>d)) :=
    (discrepancy N M u H X a _ Finset.univ H').left (crop_proper N M hK hx t H (basisInputs a) q ht)
  apply (Terms.add asks (Terms.sum Finset.univ (fun a _=>he a))).eq
  intro r x
  rw [roman N (stand (u r) ∘ X), roman N X]
  unfold combo; simp_rw [Function.comp_apply,sub_mul, Finset.sum_sub_distrib]; abel
end
end YM.FVA2.GradedFar.Pose
