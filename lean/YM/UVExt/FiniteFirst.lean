import YM.UVExt.RelayDetector

/-!
# First lattice difference on actual separated primary kernels

This estimate does not discard coordinate-projection ties. It uses a further **period/mesh
data** receipt via `Next.Extract.Base` as in the actual production of `Final`, not just a
conditional Wightman story. At this stage bounds are late in both filters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open Bid Set Filter Function MeasureTheory Extraction Extraction.Lease Dash Wilson Table
open Lattice (Site Cover wrap)
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

lemma one_shift {n N p : ℕ} (q : Fin n→C.book.Token) (i : Fin n) (a : Axis) (z) :
    featuring (heighten C (q i).1 (q i).2 a) q i N p z = ((C.S.a N:ℂ)⁻¹)*
      (C.numeric N p q (z + Work.D03.jump i a) - C.numeric N p q z) := by
  let v : Shot C.book := ⟨n,i,q,0⟩
  have hv : v.record (q i).2=q := by unfold Shot.record; change update q i (q i)=q; exact Function.update_eq_self ..
  convert Work.D03.featuring_heighten (q i).2 v a z using 1
  rw [hv]


def FiniteFirstDifference (C : Family G) (f : Extraction.Order) : Prop :=
  ∀ n (q : Fin n→C.book.Token) (K : Set (Points n)), IsCompact K → K ⊆ conf n → ∃ A : ℝ, 0≤A ∧ f.late fun N p=>
    ∀ r : Fin n → Cover, tag (C.S.a N) r ∈ K → ∀ (i : Fin n) (a : Axis),
       (C.S.a N)⁻¹ * ‖lifted C N p q (r+Work.D03.jump i a) - lifted C N p q r‖ ≤ A

lemma visits_linear {n : ℕ} (q : Fin n→C.book.Token) (i:Fin n) (d : ℕ) (x : Fin n → Cover) (N p : ℕ) :
    IsLinearMap ℂ (fun v=> featuring (visits C d v) q i N p (wrap _ ∘ x)) := by
  let t := wrap (C.side N p) ∘ x
  let L (U:Config G (C.side N p)) := ∏ j ∈ Finset.univ.erase i, C.seen (q j) (t j) U
  let v : Shot C.book := ⟨n,i,q,0⟩
  have hi (y : C.label d) : Integrable (fun U=> C.O N p y (t i) U * L U) (law G (C.side N p) (C.beta N p)) :=
    continuous_integrable _ ((C.continuousO ..).mul (continuous_finsetProd _ fun j hj=> C.continuousO ..))
  have h (y : C.label d) : featuring (visits C d y) q i N p t= moment (C.beta N p) (fun U => C.O N p y (t i) U*L U) := by
    unfold featuring
    congr 1
    funext U
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_pos rfl]
    unfold visits upper
    congr 1
    exact Finset.prod_congr rfl fun j hj=>if_neg (Finset.ne_of_mem_erase hj)
  let M:= C.linearO N p d (t i)
  change IsLinearMap ℂ (fun u => featuring (visits C d u) q i N p t)
  simp_rw [h]
  constructor
  · intro u v; unfold moment
    simp_rw [M.map_add,Pi.add_apply, add_mul]; exact integral_add (hi u) (hi v)
  intro b u; change _=(b:ℂ)* _; unfold moment; simp_rw [M.map_smul,Pi.smul_apply,smul_eq_mul, mul_assoc]
  exact integral_const_mul ..
private lemma lifted_target {n : ℕ} (q : Fin n→C.book.Token) (i:Fin n) (d : ℕ) (v : C.label d) (x N p) :
    featuring (visits C d v) q i N p (wrap (C.side N p) ∘ x)= lifted C N p (update q i ⟨d,v⟩) x := by
  rw [lifted,Family.num,featuring,moment]
  apply integral_congr_ae (Eventually.of_forall fun U=>?_)
  apply Finset.prod_congr rfl; intro j hj
  by_cases h : i=j; · subst j; rw [if_pos rfl,update_self]; rfl
  rw [if_neg (Ne.symm h),update_of_ne (Ne.symm h)]

lemma tight_bound (hb : Bound C f) {n d : ℕ} (w : Rowe C d) (ht : tight C f w)
    (q : Fin n→C.book.Token) (i : Fin n) (K : Set (Points n)) (hK : IsCompact K) (hk : K ⊆ conf n) :
    ∃ A:ℝ, 0≤A ∧ f.late fun N p=> ∀ x, tag (C.S.a N) x ∈ K → ‖featuring (upper C w) q i N p (wrap _ ∘ x)‖ ≤ A := by
  obtain ⟨R,hR⟩ := ht; let F := C.labels.level d; let M:=F.Index
  let v : M → C.label d := fun i=> Pi.single i 1
  have h (m:M) := hb.volume n (update q i ⟨d,v m⟩) K hK hk
  choose A ha hA using h
  refine ⟨(∑ x, A x)* |R|,by positivity [Finset.sum_nonneg (s:=Finset.univ) (f:=A) (fun i _=>ha i)],?_⟩
  dsimp [Order.late] at hA hR ⊢
  filter_upwards [eventually_all.mpr hA,hR] with p hs hp
  filter_upwards [eventually_all.mpr hs,hp] with N hN hz x hx
  let y : C.label d := w (f.mesh N,f.per p); let T : C.label d → ℂ := fun v=> featuring (visits C d v) q i (f.mesh N) (f.per p) (wrap _ ∘ x)
  let T' := (visits_linear q i d x (f.mesh N) (f.per p)) |>.mk' T
  change ‖T' y‖ ≤ _
  have hy (m:M) : ‖y m‖ ≤ |R| := ((norm_le_pi_norm y m).trans hz).trans (le_abs_self _)
  change _ ≤ (∑ i:M,A i)* |R|
  have he : y=∑ i : M, y i • v i := funext fun m => by
    simp only [v,Pi.smul_apply,Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem (by exact m : M) (Finset.mem_univ _)]
    · simp
    intro i hi hn; rw [Pi.single_eq_of_ne hn.symm]; rw [smul_zero]
  conv_lhs => rw [he, map_sum]
  rw [Finset.sum_mul]; apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum; intro j hj; simp only [map_smul,smul_eq_mul,norm_mul]; rw [mul_comm (A j)]
  exact mul_le_mul (hy _) (show ‖T' (v j)‖ ≤ A j from (by unfold T'; change ‖T (v _)‖≤ _; unfold T; rw [lifted_target]; exact (hN _ x hx))) (norm_nonneg _) (abs_nonneg _)

set_option maxHeartbeats 600000 in
lemma first_difference (h : C.Makes) (hc : CenterPort C f) (hs : Live S) (hO : f.Ordered C S)
    (R : Bin S) (hR : ∀ d, Bin.Good R hs d) (hB : ∀ d, RelayBin C R f d) : FiniteFirstDifference C f := by
  have hC := Around.size_done h (hc.book C f)
  intro n q K hk hK
  have hΔ := Work.D03.answer h hO hC hs
  choose w hw using fun (b : ℕ) (s:Axis) (x:C.label b) => obtain_match h hc hO (hB _) (hR (b+1))
    (sober_of_cont (P:=heighten C b x s) (fun N p o=> show Continuous ((fun U=>heighten C b x s N p o U)) from ((C.continuousO _ _ b x _).sub (C.continuousO ..)).const_smul _)) (hΔ b x s) ((hB _).pace x s)
  obtain ⟨δ,hδ,hSep⟩:= Gaps.someGrows C.S hk hK
  let I := Fin n × Axis
  let y (i:I) := w (q i.1).1 i.2 (q i.1).2
  have hz (i:I) := tight_bound hC (y i) (hw _ _ (q i.1).2|>.1) q i.1 K hk hK
  choose A hA hQ using hz; have hq (i:I) := hw _ i.2 (q i.1).2 |>.2 _ q i.1 δ 1 hδ (by norm_num)
  refine ⟨(∑ i ∈ Finset.univ, (A i+1)),Finset.sum_nonneg (s:=Finset.univ) (f:=fun i=>A i+1) (fun i _=>by linarith [hA i]),?_⟩
  dsimp only [Order.late] at hQ hq ⊢
  filter_upwards [eventually_all.mpr hQ, eventually_all.mpr hq,f.per.cofinal.eventually hSep] with p hq' he h'
  filter_upwards [eventually_all.mpr hq', eventually_all.mpr he] with N hf hd r hr i a
  let s : I := (i,a); let n' := f.mesh N; let p' := f.per p; let x : Fin n →Lattice.Site (C.side n' p') := (wrap _ ∘ r)
  calc
    _ = ‖featuring (heighten C (q i).1 (q i).2 a) q i n' p' x‖ := by
      rw [one_shift]; simp only [norm_mul,norm_inv, Complex.norm_real, Real.norm_of_nonneg (by exact (C.S.a_pos n').le)]
      have he (r : Fin n → Cover) : wrap (C.side n' p') ∘ (r+Work.D03.jump i a) = (wrap _ ∘ r) + Work.D03.jump i a := by
        funext j; unfold Work.D03.jump; by_cases hv : i=j
        · subst j; simp [Lattice.wrap_step]
        simp [Pi.single_eq_of_ne (Ne.symm hv)]
      change _ * ‖C.numeric n' p' q _ - lifted C n' p' q r‖ = _ * ‖C.numeric n' p' q _ - lifted C n' p' q r‖
      rw [he]
    _ ≤ 1 + A s := le_trans (sub_le_iff_le_add.mp (norm_sub_norm_le _ _|>.trans (hd s _ fun i j hij=>
        Gaps.gridSeparation C.S x rfl (h' _ hr) j i hij.symm))) (add_le_add_right (hf s r hr) _)
    _ ≤ _ := (by rw [add_comm]; exact Finset.single_le_sum (s:=Finset.univ) (f:=fun i=>A i+1) (fun i _=>by linarith[hA i]) (Finset.mem_univ s))
end YM.UVExt
