import YM.SchemeConversionRG11.FirstW.Hart.Native
/-! Scaled limits of any single native polynomial. Only highest coefficients survive. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Lattice Pert MultiNext.SignedSource Topology Filter Align
open Laurent (size)
open scoped BigOperators Classical
variable {d : ℕ} {p : Cover→ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
section
variable {f : Cover → E}
lemma loft_up {k : ℕ} (h:f∈Loft E (k+1)) (i : Axis) : up i f∈Loft E k := fun b hb=> by rw [combine_up]; change combine (i::b) f=0; exact h (i::b) (by rw [List.length_cons,hb])
lemma loft_basis (h : f∈Loft E 0) (x : Cover) : f x=f 0 := by
  have he := congrFun (loft_tail h) x; exact sub_eq_zero.mp (show f x-f 0=0 by simpa [Newt.tail,Newt.take,Newt.piece] using he)
lemma loft_scoped (k m : ℕ) (f: Cover→E) (H : f∈Loft E (m+k)) (D : List Axis) (h:D.length=k) : combine D f∈Loft E m := by
  intro l hl
  rw [←append_op]; exact H _ (by rw [List.length_append,h,hl]; omega)
lemma loft_scale (k : ℕ) (H : f ∈ Loft E k) : ∃ C>0,∀ x, ‖f x‖ ≤ C*(stepY x)^k := by
  have he : ∀ x,f x=∑ i∈Finset.range (k+1),Newt.piece i f (Pattern.xyz x) := fun x=> sub_eq_zero.mp (congrFun (loft_tail H) x)
  let A:=1+∑ t:Trad k, ‖combine (List.ofFn t.2) f 0‖
  have hA : 0<A:= add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun t _=>norm_nonneg _)
  let F (i:ℕ):= (4*((i:ℝ)+1))^i *4^i*A
  refine ⟨1+ ∑ i∈Finset.range (k+1), F i, add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun i _=>by unfold F; positivity)), fun x=>?_⟩
  have hV i (hi:i∈Finset.range (k+1)) := Newt.component i f hA.le (fun l (hl:l.length=i) => show ‖Newt.iterate f l 0‖≤A from by rw [switch_order]; obtain ⟨t,ht⟩:=lists l (d:=k) (by rw [hl]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)); exact (ht ▸ Finset.single_le_sum (s:=Finset.univ) (f:=fun s:Trad k=> ‖combine (List.ofFn s.snd) f 0‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ t)).trans (le_add_of_nonneg_left (by norm_num))) x
  nth_rw 1 [he x]; apply le_trans (norm_sum_le ..)
  rw [add_mul,Finset.sum_mul]
  have hx0:= unit_stepY x
  refine le_trans (Finset.sum_le_sum fun i hi=> le_trans (hV i hi) ?_) (le_add_of_nonneg_left (by positivity))
  have hm : ((size x:ℕ):ℝ) ≤ 4 * ((yard x:ℕ):ℝ) := by exact_mod_cast size_yard x
  have hx : 1+ ((size x:ℕ):ℝ) ≤ 4*stepY x := by unfold stepY; linarith
  grw [hx]; rw [mul_pow _ (stepY x)]; unfold F; grw [pow_le_pow_right₀ hx0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]; apply le_of_eq; ring
-- Continuum physical scaled pol limits at variable positions
variable {T : Itinerary}
def dialP : ℕ → (Cover→E) → E4 → E
| 0,f,_=> f 0
| i+1,f,x => ((↑i:ℝ)+1)⁻¹ • ∑ a:Axis,x a • dialP i (up a f) x
lemma crop (n : ℕ) (f : Cover → E) (z : E4) (u : ℕ→E4) (h : ℕ→ℝ) (hh:Tendsto h atTop (𝓝 0)) (hz:Tendsto (fun i=> h i • u i) atTop (𝓝 z)) : Tendsto (fun i=> h i^n • Newt.piece n f (u i)) atTop (𝓝 (dialP n f z)) := by
  induction n generalizing f u with
  | zero=>simp [Newt.piece,dialP]
  | succ n ih=>
    let k := ((n:ℝ)+1)⁻¹
    have e (a : Axis) : Tendsto (fun i=> h i • (u i - basis a)) atTop (𝓝 z) := by simp_rw [smul_sub]; simpa only [zero_smul,sub_zero] using hz.sub (hh.smul_const (basis a))
    have hv (a:Axis): Tendsto (fun i=>h i * (u i a)) atTop (𝓝 (z a)) := (PiLp.continuous_apply 2 (fun _ : Axis=>ℝ) a).continuousAt.tendsto.comp hz
    have ht := tendsto_finsetSum (s:=Finset.univ) (fun a _=> (hv a).smul (ih (up a f) _ (e a)))
    have hc := Tendsto.const_smul ht k
    rw [dialP]; apply hc.congr; intro i
    rw [Newt.piece, smul_comm _ (k:ℝ),Finset.smul_sum -- outer wrong
     ]
    dsimp only
    unfold k; simp only [Finset.smul_sum,smul_smul,pow_add,pow_one]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [show Newt.jump f a=up a f from rfl]; apply congrArg (· • _);ring
lemma cropped (k : ℕ) (f : Cover→E) (H : f∈Loft E k) (z : E4) (u : ℕ→Cover) (h : ℕ→ℝ) (hh : Tendsto h atTop (𝓝 0)) (hu : Tendsto (fun i=>Full.incVec (h i) (u i)) atTop (𝓝 z)): Tendsto (fun i=> h i^k • f (u i)) atTop (𝓝 (dialP k f z)) := by
  let W (i:ℕ) := Pattern.xyz (u i)
  have he (j) : Tendsto (fun i=> h i^j • Newt.piece j f (W i)) atTop (𝓝 (dialP j f z)) := crop j f z W h hh (show _ from hu)
  have hp (i:ℕ) : f (u i) =(∑ j∈Finset.range k, Newt.piece j f (W i))+ Newt.piece k f (W i) := by
     rw [show f (u i)=_ from sub_eq_zero.mp (show f (u i)- Newt.take (k+1) f (u i)=0 from congrFun (loft_tail H) (u i)), Newt.take, Finset.sum_range_succ]
  have hx (j:ℕ)(hj:j∈Finset.range k): Tendsto (fun i=> h i^k • Newt.piece j f (W i)) atTop (𝓝 0) := by
    have hm:j<k:=Finset.mem_range.mp hj; have hP: k-j ≠0:=by omega
    simpa only [zero_pow hP,smul_smul, zero_smul,←pow_add,Nat.sub_add_cancel hm.le] using (hh.pow (k-j)).smul (he j)
  simp only [hp, smul_add,Finset.smul_sum]; simpa only [Finset.sum_const_zero,zero_add] using (tendsto_finsetSum _ hx).add (he k)
end
end YM.RG11.FirstW
