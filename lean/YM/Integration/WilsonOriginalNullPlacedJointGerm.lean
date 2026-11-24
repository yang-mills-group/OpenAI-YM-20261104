import YM.Integration.WilsonOriginalNullPlacedGermMap
import YM.Integration.WilsonCenteredCommonGerm

/-! Read the measured germ of a sum on its two original Wilson carriers.
The two budgets and the two stored hard families enter separately. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedJointGerm
open Function Filter Lattice RG Wilson WardBin.Lies Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open ProjectorNext.Equivariance Next.Foundations Push.Local WilsonCapturedPrimaryReading
open scoped Classical Topology ContDiff
variable {G:Gauge} {n:Side} {d:ℕ} {A:Hol G} {F:Frame G d} {S:SectionData F} {o:Site n}

private theorem on_line {f:Config G n→ℂ} (hf:HasOrderAt f 1 d) (p:Probe G d) (θ:ℝ) :
    ContDiffAt ℝ (p.2.val:WithTop ℕ∞) (f ∘ A.testLinks d o (θ • p.1)) 0 := by
  let b:=testLog A d o (θ • p.1)
  have smooth:ContDiffAt ℝ (d:WithTop ℕ∞) (f ∘ increment 1) (b 0):=by
    rw [show b 0=0 from testLog_zero ..];exact hf
  have same:f ∘ A.testLinks d o (θ • p.1)=ᶠ[𝓝 0] (f ∘ increment 1) ∘ b:=
    (increment_testLog A d o (θ • p.1)).fun_comp f
  exact ((smooth.comp 0 ((testLog_diff A d o (θ • p.1)).of_le (show (d:WithTop ℕ∞) ≤ ω from le_top))).congr_of_eventuallyEq same).of_le
    (by exact_mod_cast (Nat.le_of_lt_succ p.2.isLt))

theorem add {f g:Config G n→ℂ} (hf:HasOrderAt f 1 d) (hg:HasOrderAt g 1 d) (p:Probe G d) (θ:ℝ) :
    jet A p θ o (f+g)=jet A p θ o f+jet A p θ o g := by
  exact iteratedDeriv_fun_add (on_line (A:=A) (o:=o) hf p θ) (on_line (A:=A) (o:=o) hg p θ)

variable (C:Family G) (rank N per i:ℕ)
local notation "F₀" => C.labels.level rank
local notation "S₀" => C.localSection rank
local notation "P₀" => C.path.rep N per i

theorem original (H:C.Makes) (live:i ≤ N) (home:Opened C rank i per) (site:Site (C.side i per))
    (W:Rep G (C.side i per)) (same:W.p=(P₀).p) (quiet:∀ U,W.eval U=(P₀).eval U)
    (z h k:Coefficient F₀ (C.side i per)) {u v w a b c:ℝ}
    (zf:z.Format site C.params P₀) (zp:z.remBound site P₀ u a)
    (hf:h.Format site C.params W) (hp:h.remBound site W v b)
    (kf:k.Format site C.params P₀) (kp:k.remBound site P₀ w c)
    (field:∀ U,z.density site S₀ P₀ U=h.density site S₀ W U+k.density site S₀ P₀ U) :
    projection F₀ C.params (P₀).p.threshold site z=
      projection F₀ C.params W.p.threshold site h+projection F₀ C.params (P₀).p.threshold site k := by
  have dims:=dimensions rank N per i H home.post live
  have so:=H.sections rank
  have fit:=H.places rank i per home.post
  have sectionPath:=sections_visit H home.post site
  have zd:=WilsonCapturedPrimarySmooth.original so dims.1 sectionPath zf zp
  have kd:=WilsonCapturedPrimarySmooth.original so dims.1 sectionPath kf kp
  have dW:rank ≤ W.p.order:=same.symm ▸ dims.1
  have pW:rank ≤ W.p.power:=same.symm ▸ dims.2
  have hd:=WilsonCapturedPrimarySmooth.original so dW sectionPath hf hp
  have raw:reading S₀ P₀ site z=reading S₀ W site h+reading S₀ P₀ site k:=by
    funext U;unfold reading;simp only [Pi.add_apply];rw [field U,quiet U,add_div]
  apply probes_injective F₀
  intro p
  rw [map_add,WilsonCapturedPrimaryReading.probe so fit dims.1 dims.2 sectionPath zf zp zd,
    WilsonCapturedPrimaryReading.probe so fit dW pW sectionPath hf hp hd,
    WilsonCapturedPrimaryReading.probe so fit dims.1 dims.2 sectionPath kf kp kd,raw,same]
  exact add hd kd p (P₀).p.threshold

end YM.Integration.WilsonOriginalNullPlacedJointGerm
