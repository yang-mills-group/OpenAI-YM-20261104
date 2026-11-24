import YM.MSbar.Pole.Scale.Recess

/-! # Regular-in-dimension effective amplitude differing off positive radii and zero.
`Soft` is auxiliary to UV proof; allows one to take Laurent coefficients and flow
differential distinctly. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin
open scoped Topology ContDiff BigOperators Classical Interval
variable {I : Type} [Fintype I]

/-- At fixed positive scale, meromorphic amplitude with no pole. Every evaluation
in actual tensor dimension is also real `C¹` including kinematics of that scale,
as allowed below (fixed evaluation). -/
structure Soft (F : ℝ → ℂ → Cloud I) : Prop where
  vortex s : 0<s → Vortex 0 (F s)
  discrete r : 0<r → ∀ n x, ∃ g : ℝ × ℂ→ℂ, ContDiffAt ℝ 1 g (r,0) ∧
       ∀ᶠ w in nhds (r,(0:ℂ)), w.2 ≠ 0 → F w.1 w.2 n x=g w

variable {F G: ℝ → ℂ → Cloud I}
namespace Soft
lemma zero : Soft (0 : ℝ → ℂ → Cloud I) := ⟨fun _ _=>Vortex.zero _,fun _ _ _ _=>⟨fun _=>0,contDiffAt_const,Eventually.of_forall fun _ _=>rfl⟩⟩
lemma add (h : Soft F) (hh : Soft G): Soft (F+G):= by
  refine ⟨fun r hr=>(h.vortex _ hr).add (hh.vortex _ hr),fun r hr n x=>?_⟩
  obtain ⟨A,ha,he⟩:=h.discrete _ hr n x; obtain ⟨B,hb,hE⟩:=hh.discrete r hr n x; exact ⟨A+B,ha.add hb,(he.and hE).mono fun v h hz=>congr_arg₂ (·+·) (h.1 hz) (h.2 hz)⟩
lemma sum {Z : Type*} (s : Finset Z) (f : Z→ℝ→ℂ→Cloud I) (h : ∀ z∈s, Soft (f z)) : Soft (∑ z∈s,f z):=by
  induction s using Finset.induction_on with
  | empty=>simpa using (zero (I:=I))
  | @insert a s ha ih=> rw [Finset.sum_insert ha]; exact add (h a (Finset.mem_insert_self ..)) (ih fun i hi=>h i (Finset.mem_insert_of_mem hi))

lemma backside (h : Soft F) (he : ∀ (s:ℝ) (z:ℂ),0<s→ z≠0→ F s z=G s z) : Soft G := by
  refine ⟨fun s hs=>(h.vortex s hs).congr (r:=1) zero_lt_one (fun z hz=>(he _ _ hs hz.2).symm), fun r hr n x=>?_⟩
  obtain ⟨A,ha,hA⟩:=h.discrete _ hr n x; refine ⟨A,ha,?_⟩
  filter_upwards [hA, IsOpen.mem_nhds (isOpen_lt continuous_const continuous_fst) (show 0<(r,(0:ℂ)).1 from hr)] with w hw hh h'
  rw [← he _ _ hh h',hw h']
end Soft

lemma singleMove (A : Finset I) (t:ℝ) {R : ℝ} {G : ℂ → Cloud I} (h : Meridian (zone R) G) : Meridian (zone R) (fun z n x=>G z n (move A t x)) := by
  constructor
  · intro n; have h' := (h.budget n).pull (p:=ticket _) (r:=ticket (@id _)) (s:=1) (walks A t n) ?_ (Bills.const _)
    · simpa only [walks_on] using h'
    let L := walks A t n; refine bill_single (C:=1+‖L‖) (l:=1) (by positivity) fun x hx=>?_
    change ‖1+‖L x‖‖ ≤ _ * (1+‖x‖)^1
    rw [Real.norm_of_nonneg (by positivity),pow_one]; nlinarith [L.le_opNorm x,norm_nonneg L,norm_nonneg x]
  intro z hz; refine ⟨fun n J x=> ?_,fun n x=>?_⟩
  · rw [move_turn,(h.tensor z hz).moves]
  rw [move_pad,(h.tensor z hz).agrees]

lemma roll_meridian (A:Finset I)(d:Age) {R:ℝ} {F:ℂ→Cloud I} (h:Meridian (zone R) F) (s:ℝ)(hs:0<s): Meridian (zone R) (roll A d s F):=by
  have ht := (singleMove A s h).weight (b:=fun z => (s:ℂ)^(d.alpha z)) ?_ R (fun u hu=>((zone_mem ..).mp hu).le)
  · rw [show roll A d s F=(fun z n x=> F z n (move A s x) * (s:ℂ)^d.alpha z) by funext; exact mul_comm ..]; exact ht
  simp_rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hs.ne' : (s:ℂ)≠0),Age.alpha]; fun_prop
lemma roll_vortex (A:Finset I)(d:Age) {k:ℕ} {F:ℂ→Cloud I} (h:Vortex k F) {s:ℝ}(hs:0<s): Vortex k (roll A d s F):=by
  obtain ⟨R,Z,hr,H,hh⟩:=h; refine ⟨R,roll A d s Z,hr,roll_meridian A d H s hs, fun z hz n x=>?_⟩
  unfold roll; rw [mul_left_comm, hh z hz]

lemma curve_diff (A : Finset I) {n:ℕ} (x:External I n) : ContDiff ℝ ∞ (fun t:ℝ=>move A t x) := by simp_rw [moving]; fun_prop
lemma ribbon (A : Finset I) (d : Age) {s : ℝ} (hs:0<s) {U : ℝ} (hu:0<U) {F:ℂ→Cloud I} (h:Meridian (zone U) F) (n:ℕ)(x:External I n) :
    ContDiffAt ℝ 1 (fun w:ℝ × ℂ=>roll A d w.1 F w.2 n x) (s,0) := by
  unfold roll; apply ContDiffAt.mul
  · have he : ContDiffAt ℝ 1 (fun w:ℝ × ℂ=> Complex.exp ((Real.log w.1:ℂ) * d.alpha w.2)) (s,0) := by
      apply ContDiffAt.cexp; refine ContDiffAt.mul ?_ (by unfold Age.alpha; fun_prop)
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (ContDiffAt.log contDiffAt_fst hs.ne')
    refine he.congr_of_eventuallyEq ?_
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_fst) (show 0<(s,(0:ℂ)).1 from hs)] with t ht
    have hh: (t.1:ℂ)≠0:= by exact_mod_cast (show 0<t.1 from ht).ne'
    simp only [Complex.ofReal_log (show 0<t.1 from ht).le,Complex.cpow_def_of_ne_zero hh]
  have hp : ContDiffAt ℝ 1 (fun z:ℝ × ℂ=> (z.2,move A z.1 x)) (s,0) := contDiffAt_snd.prodMk (((curve_diff A x).of_le (by norm_cast)).contDiffAt.comp _ contDiffAt_fst)
  exact ((show ContDiffAt ℝ 1 (fun i:ℂ × External I n=> F i.1 n i.2) ((0:ℂ),move A s x) from (h.budget n).stream.localn 1 (mem_prod.mpr ⟨zone_zero hu,mem_univ _⟩)).comp (s,(0:ℂ)) (f:=fun z:ℝ × ℂ=> (z.2,move A z.1 x)) hp)

lemma rolled (A:Finset I)(d:Age) {F:ℂ→Cloud I} (h : Vortex 0 F) : Soft (fun r=> roll A d r F) := by
  refine ⟨fun r hr=>roll_vortex _ _ h hr,fun r hr n x=>?_⟩
  obtain ⟨R,G,hp,H,h⟩:=h; refine ⟨_,ribbon A d hr hp H n x, ?_⟩
  filter_upwards [IsOpen.mem_nhds (isOpen_Ioi.prod (show IsOpen (zone R) from Metric.isOpen_ball)) (mem_prod.mpr ⟨hr,zone_zero hp⟩)] with p hp h'
  unfold roll; congr 1; simpa using h p.2 ⟨hp.2,h'⟩ n (move A p.1 x)
end YM.MSbar.Pole
