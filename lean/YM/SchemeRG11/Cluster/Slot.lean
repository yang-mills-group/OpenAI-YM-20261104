import YM.SchemeRG11.Bubble.Ample

/-!
Dimensionally prescribe cubic vertex integration. On each triple of Schwinger
TIMES perform the integrated gauge-vertex Gaussian in d dimensions first.
Do NOT take d-angular averages/d contractions on physical projected tensors at
finite time. Planes arbitrary. All mark displacements for this formula distinct.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SchemeRG11.Cluster
open Set MeasureTheory Filter Metric Function Hot MSbar
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {n : ℕ}
abbrev Eye := Fin 3
abbrev Nodes (n : ℕ) := Eye→Space n
abbrev Time := ℝ × ℝ × ℝ

def moment (p : Time) : Eye→ℝ := ![p.1,p.2.1,p.2.2]
lemma moment_c (i: Eye) : Continuous fun p=>moment p i := by fin_cases i <;> first | exact continuous_fst | exact continuous_fst.comp continuous_snd | exact continuous_snd.comp continuous_snd

def knot (p : Time) := p.1*p.2.1+p.1*p.2.2+p.2.1*p.2.2

def fork (p : Time) (i : Eye) := moment p i / knot p

def bevel (i : Eye) (u : Nodes n) := ‖u (i+1)-u (i+2)‖^2/4
lemma bevel_c (i : Eye) : ContDiff ℝ ∞ (bevel i (n:=n)) := by
    let f (j : Eye) : ContDiff ℝ ∞ (fun p : Nodes n=> p j) := contDiff_apply ℝ (Space n) j
    exact ((contDiff_norm_sq ℝ (E:=Space n)).comp ((f (i+1)).sub (f (i+2)))).div_const _

def openZen := Ioi (0:ℝ)
def tripod : Set Time := openZen ×ˢ openZen ×ˢ openZen
lemma tripod_meas : MeasurableSet tripod := measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi)

def clearance (n : ℕ) : Set (Nodes n) := {x | ∀ i : Eye, 0<bevel i x}
lemma clearance_open : IsOpen (clearance n) := by
  rw [show clearance n=⋂ i:Eye, bevel i ⁻¹' (Ioi 0) by ext; simp [clearance]]
  exact isOpen_iInter_of_finite (fun i=> isOpen_Ioi.preimage (bevel_c i).continuous)
lemma lit (p : Time) (h : p∈tripod) (i : Eye): 0<moment p i := by fin_cases i; exact h.1; exact h.2.1; exact h.2.2
lemma globe (p : Time) (h : p∈tripod) : 0 < knot p :=
   add_pos (add_pos (mul_pos (lit _ h 0) (lit _ h 1)) (mul_pos (lit _ h 0) (lit _ h 2))) (mul_pos (lit _ h 1) (lit _ h 2))

/-- A single occurrence of the vertex. Costs `c(e)^2` not `c(e)^3` due to action normalization. -/
def braid (μ : ℝ) (p : Time) (z : ℂ) (x : Nodes n) :=
    (knot p:ℂ)^(z-2)*Complex.ofReal (Real.exp (-∑ i,fork p i*bevel i x))*Pole.factor μ z^2
abbrev Sweep (n : ℕ) := List (Nodes n)

def spin (μ : ℝ) (l : Sweep n) (p : Time) (e : ℂ) : Nodes n→ℂ := series (braid μ p e) l

lemma plugs {μ : ℝ} (h : 0<μ) (l : Sweep n) : ∃ Q : Tint Eye (Nodes n), ∀ p e,
    spin μ l p e=tongs bevel Q (knot p) (fork p) e := by
  let P : Tint Eye (Nodes n):= Tint.number _ ((Pole.factor_entire μ h).pow 2)
  obtain ⟨Q,h⟩:=recast bevel_c P l
  exact ⟨Q,fun p e=> h (knot p) (fork p) e⟩

variable {μ : ℝ} (hμ : 0<μ)
include hμ
lemma crew (l : Sweep n) {p : Time} (hp : 0 < knot p) {X : Type} [TopologicalSpace X] {x : X}
    {g : X→Nodes n} {F : X→Time} {e : X→ℂ} (hg : ContinuousAt g x) (hF : ContinuousAt F x) (he : ContinuousAt e x) (hx : F x=p) :
    ContinuousAt (fun y=> spin μ l (F y) (e y) (g y)) x := by
  have hh : Continuous knot := by unfold knot; fun_prop
  obtain ⟨Q,h⟩:=plugs hμ l; subst p
  have ht := hh.continuousAt.comp (f:=F) hF
  have hu : ContinuousAt (fun y=>fork (F y)) x := continuousAt_pi.mpr (fun i=> ((moment_c i).continuousAt.comp (f:=F) hF).div ht hp.ne')
  simp only [h]; exact tackle (fun i=> (bevel_c i).continuous) Q ht hu he hg hp.ne'
lemma webs (l : Sweep n) (p : Time) (hp : 0<knot p) (x : Nodes n) : Differentiable ℂ (fun e=> spin μ l p e x) := by
  obtain ⟨Q,h⟩:= plugs hμ l; simp only [h]; exact tunnel _ _ hp _ _
end YM.SchemeRG11.Cluster
