import YM.Integration.WilsonOriginalNullShadow
import YM.Trace.Physicalv2.Germ

/-! The zero jet of the canonical nonlinear source and the measured coordinate
use the same actual unit. Nonunit primary fields therefore qualify for the
physical zero-horizon estimate at a displaced site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullFlatPrimary
open Labels Lattice Wilson RG Source Trace.Physical.Germ Next.Foundations Extra.Histories
open Push.Local
open scoped Classical BigOperators Topology
variable {G:Gauge} {n:Side} {d:ℕ} (F:Frame G d) (A:Hol G)

theorem read_zero (x:F.Coeff) : read (0:Jet G) (F.coords.symm x).val=x 0 := by
  have project : F.scaled 0 x = (x 0) • F.e0 := by
    funext i
    by_cases h : i=0
    · subst i; simp [F.zero_degree,Frame.e0]
    · have h' := (F.factors_pos i h).ne'
      simp [h',Frame.e0,h]
  have exactRead := read_frame_scaled (0:Jet G) F x 0
  rw [project,zero_smul,←F.coords_unit,map_smul,LinearEquiv.symm_apply_apply] at exactRead
  simpa [unit] using exactRead.symm

theorem placed (S:SectionData F) (sound:S.Sound A) (o:Site n) (θ:ℝ) (v:F.Coeff) :
    presented S o θ v 1 = v 0 := by
  let w := F.scaled θ⁻¹ v
  have h := (sound.projects w (0:Jet G)).2.2 0 (Nat.zero_le _)
  have exactZero : scaleJet (0:Jet G) (0:ℝ)=0 := by funext j; simp [scaleJet]
  simp only [iteratedDeriv_zero,A.flat,exactZero] at h
  change S.evaluate w 1 = v 0
  exact h.trans ((read_zero F w).trans (by simp [w,F.zero_degree]))

theorem rank_zero (R:Rep G n) (X:Support n) (o:Site n) (f:Config G n→ℂ)
    (anchor:o∈X) (shape:R.p.Regular X f) (zero:f 1=0) : RegFit R o 0 A X f := by
  refine ⟨shape,anchor,zero,fun _ J=>⟨(computed A shape o (Nat.zero_le _) J).1,?_⟩⟩
  intro a h
  obtain rfl := Nat.eq_zero_of_le_zero h
  have flat : A.testLinks 0 o J (0:ℝ)=1 := by funext l; simp [Hol.testLinks,A.flat]
  simpa only [iteratedDeriv_zero,flat] using zero

theorem canonical (S:SectionData F) (R:Rep G n) (o:Site n) {w:ℝ} (reader:Readable A S R.p n w)
    (v:F.Coeff) :
    RegFit R o 0 A (S.footprint o) (presented S o R.p.threshold (F.core v)) ∧
    R.p.supBounds o (S.footprint o) (presented S o R.p.threshold (F.core v)) (w*F.coeffSize (F.core v)) := by
  obtain ⟨shape,fee⟩ := presented_good o reader (F.core v)
  have z := placed F A S reader.sound o R.p.threshold (F.core v)
  obtain anchor : o∈S.footprint o := Finset.mem_image.mpr ⟨0,reader.sound.anchored,by simp⟩
  exact ⟨rank_zero A R _ o _ anchor shape (z.trans (by simp [Frame.core])),fee⟩

theorem unit_germ (R:Rep G n) (o:Site n) (P:Coefficient F n) (shape:P.Format o A R)
    (order:d≤R.p.order) : projection F A R.p.threshold o P 0=P.x 0 := by
  have atom (i:ℕ) : vector F A R.p.threshold o (P.regular i) 0=0 := by
    let z := label A o (P.regular i) d
    have h := (computed A (shape.smooth i) o order (0:Jet G)).2.2 0 (Nat.zero_le _)
    have flat : A.testLinks d o (0:Jet G) (0:ℝ)=1 := by funext l; simp [Hol.testLinks,A.flat]
    have exactZero : scaleJet (0:Jet G) (0:ℝ)=0 := by funext j; simp [scaleJet]
    have wz : read (0:Jet G) z.val=0 := by
      simpa only [iteratedDeriv_zero,flat,exactZero,shape.identity_null] using h.symm
    have coord : (F.coords z) 0=0 := by
      rw [←read_zero F (F.coords z),LinearEquiv.symm_apply_apply]
      exact wz
    simpa [vector,z,F.zero_degree] using coord
  let v i := vector F A R.p.threshold o (P.regular i)
  change P.x 0 + (∑'i,v i) 0=P.x 0
  by_cases finite:Summable v
  · rw [tsum_apply finite]; simp [v,atom]
  · rw [tsum_eq_zero_of_not_summable finite];simp

end YM.Integration.WilsonOriginalNullFlatPrimary
