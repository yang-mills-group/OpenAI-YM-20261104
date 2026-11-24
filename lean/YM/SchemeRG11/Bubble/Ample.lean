import YM.SchemeRG11.Bubble.Yoke
/-!
Reading rules for the b - gauge-action double-line, per open monomial.
The integrated gauge vertex has an open external A leg and b an open external
F slot; treat their derivatives as independent for the local pole, unamputate
after contracting Laurent coefficients in this stencil basis. This is ALREADY
a separated rule. Does NOT assert that the only OTHER poles of a bigger diagram
are local to multiple external marks (no multi-mark extensions here).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Set MeasureTheory Filter Metric Function Hot MSbar
open scoped Topology ContDiff BigOperators
variable {n : ℕ} {μ A B C : ℝ} (hμ : 0<μ) (hA : 1≤A) (hB : 1≤B) {z : ℂ}

namespace Prize
variable (g : Prize n)

def peeled (μ A B : ℝ) (p : Space n) (z : ℂ) := letters p g.word*extend μ A B g.w (vertex p) (grade p) g.rank z
def natural (μ A B : ℝ) (p : Space n) (z : ℂ) := letters p g.word*native μ A B g.w (vertex p) g.rank z
def spike (μ : ℝ) (p : Space n) :=
    letters p g.word* Pole.factor μ 0*(if g.rank then scale g.w*(-(‖p‖^2:ℝ)) else route g.w)
def inside (μ A B : ℝ) (p : Space n) (z : ℂ) := letters p g.word*glide μ A B g.w (vertex p) (grade p) g.rank z

include hμ hA hB
/-- meromorphic continuation and pole read, **in amputated density**. -/
lemma rule (p : Space n) : MeromorphicOn (peeled g μ A B p) cave ∧ AnalyticAt ℂ (inside g μ A B p) 0 ∧
    (∀ e : ℂ, 1 < e.re → peeled g μ A B p e=natural g μ A B p e) ∧
    ∀ e : ℂ, e≠0 → peeled g μ A B p e= spike g μ p/e+inside g μ A B p e := by
  have h : 1≤A+B:=by linarith
  let F:=vertex p; let D:=grade p
  obtain ⟨hp,hq⟩:= poles g.hw (amplitude p) g.rank h hμ (blade μ g.w F D g.rank 0) (fun e=>rfl)
  refine ⟨fun e he=> (analyticAt_const.meromorphicAt).mul (grope g.hw (amplitude p) g.rank h hμ e he),analyticAt_const.mul hp,fun e he=>?_,fun e he=>?_⟩
  · exact congrArg _ (extends_conv (z:=e) (μ:=μ) g.hw (amplitude p) g.rank h (by cases heq:g.rank <;> norm_num [index] <;> linarith : (index g.rank:ℕ)<e.re)).2.symm
  rw [peeled,hq _ he]
  unfold spike inside blade
  split <;> simp [D,grade,F,vertex,div_eq_mul_inv] <;> ring

/-- Open A contracted with a monomial ALSO carrying derivatives from the
insertion with which the bubble is joined. -/
def pendant (L : List (Fin n)) := g.word ++ L

def laden (μ A B C : ℝ) (L : List (Fin n)) (x : Space n) (z : ℂ) := let F:= plume μ (pendant g L);
      extend μ A B g.w (gear F C x) (stud F C x) g.rank z

def laid (μ A B C : ℝ) (L : List (Fin n)) (x : Space n) (z : ℂ) := let F:= plume μ (pendant g L);
      native μ A B g.w (gear F C x) g.rank z

/-- The same spike from `rule`, now transformed with a single `C` line.
For p field derivatives use incoming `(i p)` symbol and Fourier transform by
the same Gaussian rule as for the rest of the CT. Thus on `letters` use
`plume`; for `-p²` use the heat derivative in the propagating C Gaussian.
No pole operation HERE. -/
def scabbard (μ C : ℝ) (L : List (Fin n)) (x : Space n) (z : ℂ) := let F:= plume μ (pendant g L)
      Pole.factor μ 0*(if g.rank then scale g.w*stud F C x z else route g.w*gear F C x z 0)

def repair (μ A B C : ℝ) (L : List (Fin n)) (x : Space n) (z : ℂ) := let F:= plume μ (pendant g L);
      glide μ A B g.w (gear F C x) (stud F C x) g.rank z

theorem mirage (L : List (Fin n)) {x : Space n} (hx : x≠0) : MeromorphicOn (laden g μ A B C L x) cave ∧ AnalyticAt ℂ (repair g μ A B C L x) 0 ∧
    (∀ e : ℂ, 1 < e.re → laden g μ A B C L x e=laid g μ A B C L x e) ∧
    ∀ e : ℂ, e≠0 → laden g μ A B C L x e - e⁻¹*scabbard g μ C L x e=repair g μ A B C L x e := by
  have h : 1≤A+B:=by linarith
  have hf:= fires (hemp hμ (pendant g L)) hx C
  exact ⟨grope g.hw hf g.rank h hμ, glides g.hw hf g.rank h hμ,fun e he=> (extends_conv g.hw hf g.rank h (by cases hi:g.rank <;> norm_num [index] <;> linarith : (index g.rank:ℕ)<e.re)).2.symm,fun e he=> delivers g.rank he⟩

lemma off_axis (L : List (Fin n)) {x : Space n} (hx : x≠0) (C : ℝ) : ContinuousAt (fun x=>repair g μ A B C L x 0) x := by
  obtain ⟨K,hK,he,h⟩:= exists_compact_subset isOpen_compl_singleton (show x∈({0}ᶜ:Set _) from hx)
  have hf:=hemp hμ (pendant g L)
  obtain ⟨D,hD,hp⟩:=few hf hK (fun hu=> h hu rfl)
  have hu : ∀ᶠ y in 𝓝 x, y∈K := mem_interior_iff_mem_nhds.mp he
  exact stabilizes g.hw g.rank (hu.mono fun y hy=>fires hf (show y≠0 from h hy) C) hD
     (hu.mono fun y hy=> hp y hy C _ (by linarith)) (fun _ hr=> score hf hx C hr) (score hf.coals hx C le_rfl)
omit hA hB
lemma price (L : List (Fin n)) {K : Set (Space n)} (hk : IsCompact K) (hl : 0∉K) :
    ∃ D>0, ∀ A≥1, ∀ B≥1, ∀ C, ∀ x∈K, ‖repair g μ A B C L x 0‖ ≤ D*(A+B) := by
  obtain ⟨D,hD,hp⟩:=few (hemp hμ (pendant g L)) hk hl
  obtain ⟨E,hE,h⟩:=budget g.hw _ hD μ
  exact ⟨E,hE,fun A ha B hb C x hx=> h _ _ A B g.rank (by linarith) (hp x hx C _ (by linarith))⟩
end Prize

def earn (μ A B C : ℝ) (X Y L : List (Fin n)) (x : Space n) : ℂ := ((Awards X Y).map fun g=> g.repair μ A B C L x 0).sum
include hμ
include hA hB in
lemma earns {x : Space n} (hx : x≠0) (X Y L : List (Fin n)) : ContinuousAt (earn μ A B C X Y L) x := by
  have hh (s : List (Prize n)): ContinuousAt (fun x=> (s.map fun g=>g.repair μ A B C L x 0).sum) x := by
    induction s with
    | nil => simp; exact continuousAt_const
    | cons g s ih => simp only [List.map_cons,List.sum_cons]; exact (Prize.off_axis hμ hA hB g L hx C).add ih
  exact hh (Awards X Y)
lemma health (X Y L : List (Fin n)) {K : Set (Space n)} (hk : IsCompact K) (hl : 0∉K) :
    ∃ E>0, ∀ A≥1, ∀ B≥1, ∀ C, ∀ x∈K, ‖earn μ A B C X Y L x‖ ≤ E*(A+B) := by
  unfold earn; induction Awards X Y with
  | nil => exact ⟨1,zero_lt_one,fun A ha B hb C x hx=> by simp only [List.map_nil,List.sum_nil,norm_zero]; positivity⟩
  | cons g s ih =>
    obtain ⟨E,hE,e⟩:=ih; obtain ⟨D,hD,d⟩:=Prize.price hμ g L hk hl
    refine ⟨D+E,by positivity,fun A ha B hb C x hx=>?_⟩
    simp only [List.map_cons,List.sum_cons]; rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (d _ ha _ hb _ x hx) (e _ ha _ hb _ x hx))
end YM.SchemeRG11.Bubble
