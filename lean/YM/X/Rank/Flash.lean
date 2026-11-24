import YM.X.Rank.Lens
import Mathlib.Algebra.Module.Submodule.Union
/-!
Transverse position test: from the midpoint between two endpoints pick an
imaginary displacement orthogonal to their real difference. On the same
line **avoid all other** cones even if one of their centers is on the real
sphere. (All this is free tests only.)
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank.Rad
open Function Set Filter Submodule Polynomial
open scoped Topology BigOperators Classical InnerProductSpace
variable {a b y u v x : E4} {s:Finset E4}

lemma beam_iff : (beam u v).eval Complex.I=0 ↔ ‖u‖=‖v‖ ∧ inner ℝ u v=0 := by
  simp only [beam,eval_C,eval_X,eval_add,eval_mul, eval_pow,Complex.I_sq,neg_one_mul]
  constructor
  · intro h; have hR := congr_arg Complex.re h; have hI:= congr_arg Complex.im h
    simp only [Complex.add_re,Complex.ofReal_re,Complex.neg_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im, mul_zero, zero_mul, sub_zero,Complex.zero_re,add_zero] at hR
    simp only [Complex.add_im, Complex.ofReal_im, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.zero_im,neg_zero,zero_mul, one_mul, zero_add, add_zero] at hI; constructor
    · nlinarith [norm_nonneg u,norm_nonneg v]
    linarith only [hI]
  rintro ⟨h,hI⟩; rw [h,hI]; simp

lemma beam_eq (h:inner ℝ u v=0) : beam (-u) v=beam u v := by simp [beam,h]

private lemma perp_exists (d m : E4) (hd:d≠0)(s:Finset E4) (ha:m+d ∉ s)(hb:m-d ∉ s) :
    ∃ v:E4, ‖v‖=‖d‖ ∧ inner ℝ d v=0 ∧ ∀ x∈s,(beam (x-m) v).eval Complex.I≠0 := by
  let s' := s.filter fun x=> ‖x-m‖=‖d‖
  let P:= span ℝ ({d}:Set E4); let V := Pᗮ
  let f (x:↥s') : Submodule ℝ V := ((span ℝ ({x.val-m}:Set E4))ᗮ).comap V.subtype
  have h (x:↥s') : f x≠⊤ := by
    intro h; have he:=Finset.mem_filter.mp x.property
    have hv : x.val-m∈Vᗮ:=by
      apply (Submodule.mem_orthogonal' V _).2; intro i hi
      have he: (⟨i,hi⟩ : V) ∈ f x:= h.symm ▸ mem_top
      exact mem_orthogonal_singleton_iff_inner_right.mp he
    change x.val-m∈ Pᗮᗮ at hv; rw [P.orthogonal_orthogonal] at hv
    obtain ⟨t,ht⟩:=Submodule.mem_span_singleton.mp hv
    have hT:= he.2; rw [← ht,norm_smul] at hT; rw [Real.norm_eq_abs] at hT
    have hQ : |t|=1:=mul_right_cancel₀ (norm_ne_zero_iff.mpr hd) (hT.trans (one_mul _).symm)
    rcases le_total 0 t with no|no
    · rw [abs_of_nonneg no] at hQ; rw [hQ,one_smul] at ht
      rw [show m+d=x.val by rw [ht]; abel] at ha; exact ha he.1
    rw [abs_of_nonpos no] at hQ; rw [show t=-1 by linarith only [hQ],neg_one_smul] at ht
    rw [show m-d=x.val by rw [sub_eq_add_neg, ht]; abel] at hb; exact hb he.1
  have hV0 : Module.finrank ℝ V=3:= by
    letI : Fact (Module.finrank ℝ E4 = 3+1) := ⟨by simp [E4,Axis]⟩
    exact finrank_orthogonal_span_singleton hd
  let p : (Option ↥s') → Submodule ℝ V := fun x=> Option.elim x ⊥ f
  have hV : ∀ x,p x≠⊤ := fun x=> by cases x with
    | none=> haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (show 0< Module.finrank ℝ V by rw [hV0]; omega)
             exact bot_ne_top
    | some x=> exact h x
  obtain ⟨z,hz⟩:= exists_forall_notMem_of_forall_ne_top p hV
  have hz' : z.val ≠ 0 := fun h=> hz none ((Submodule.mem_bot ℝ).mpr (Subtype.ext h))
  let K:=‖d‖/‖z.val‖; have hk:0<K:= div_pos (norm_pos_iff.mpr hd) (norm_pos_iff.mpr hz'); let y:=K • z.val
  have ht : ‖y‖= ‖d‖:= by rw [norm_smul, Real.norm_eq_abs,abs_of_pos hk]; exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz')
  refine ⟨y,ht, mem_orthogonal_singleton_iff_inner_right.mp (V.smul_mem _ z.property),fun x hx he=> ?_⟩
  obtain ⟨hA,hB⟩:= beam_iff.mp he
  apply hz (.some ⟨x,Finset.mem_filter.mpr ⟨hx,hA.trans ht⟩⟩)
  apply mem_orthogonal_singleton_iff_inner_right.mpr
  change inner ℝ (x-m) z.val=0
  unfold y at hB; rw [real_inner_smul_right] at hB; exact (mul_eq_zero.mp hB).resolve_left hk.ne'

structure View (s:Finset E4)(a b m d v:E4):Prop where
  h₁:a-m=d
  h₂:b-m=-d
  hv:v≠0
  onBeam : (beam d v).eval Complex.I=0
  offBeam (x : E4) : x∈s → (beam (x-m) v).eval Complex.I≠0

lemma viewing (h:a≠b)(ha:a∉s)(hb:b∉s) : ∃ m d v, View s a b m d v := by
  let d:=(1/2:ℝ) • (a-b); let m:=a-d
  have h₁:m+d=a:=sub_add_cancel ..; have h₂:m-d=b:=by unfold m d; module
  obtain ⟨v,hv,hV,H⟩:= perp_exists d m (show d≠0 from smul_ne_zero (by norm_num) (sub_ne_zero.mpr h)) s (h₁.symm ▸ ha) (h₂.symm ▸ hb)
  exact ⟨m,d,v,by rw [← h₁]; abel,by rw [←h₂]; abel, norm_pos_iff.mp (hv.symm ▸ norm_pos_iff.mpr (smul_ne_zero (by norm_num) (sub_ne_zero.mpr h) : d≠0)), beam_iff.mpr ⟨hv.symm,hV⟩,H⟩

lemma clears (hv:v≠0)(u:E4)(s: Finset E4): ∀ᶠ t:ℝ in atTop,u+t • v∉s := by
  have h: Injective (fun t:ℝ=>u+t • v):= fun x y h=> smul_left_injective ℝ hv (add_left_cancel h)
  exact (h.tendsto_cofinite.mono_left atTop_le_cofinite).eventually (p:= fun p:E4=>p∈(s:Set E4)ᶜ) ((by simpa [Filter.mem_cofinite] using s.finite_toSet))
end YM.PositionX.Rank.Rad
