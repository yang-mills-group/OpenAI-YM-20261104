import YM.XSpace.LinearSection
/-! # Top Wick readout into a true invariant label before the equation quotient -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson Source Source.Drops MeasureTheory
open Next.Rank Normal Spindle Beamer Next.Foundations Configuration MvPolynomial LiftMark
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff Classical
variable {G : Gauge} {d:ℕ}

lemma colors_access (J : Snap G d) (u : G.El) : access (Cast u J)=colorPull G u (access J) := by
  funext x; rw [colorPull,revealed_cell,revealed_cell,map_sum]; apply Finset.sum_congr rfl; intro i hi
  unfold CellsInt.trail
  simp only [expand,dif_pos (Finset.mem_range.mp hi),Function.comp_apply,Cast]
  unfold CellsInt.east; simp_rw [Labels.Taylor.paint_value]
  exact (G.adjoint u).toContinuousLinearMap.intervalIntegral_comp_comm (CellsInt.east_int _ _ ((Tensor.diag_smooth _ 1).continuous))

def twists (s: Ortho) (J : Snap G d): Snap G d:= fun i=> Labels.Taylor.turn s⁻¹ (J i)
lemma twists_flash (s:Ortho) (J:Snap G d) (t:ℝ): twists s (flash J t)=flash (twists s J) t := by funext i; simp [twists,flash,Drops.trunk,expand,scaleJet,i.isLt]
lemma twists_links (s:Signed) (J:Snap G d) (t:ℝ): (hol G).links d (expand d (t • twists s.ortho J)) 1 = pull s 0 ((hol G).links d (expand d (t • J)) 1) := by
  rw [(Work.G01.answer G (hol G)).1]; congr 1
  funext i; by_cases h : i<d-1 <;> simp [expand,h,twists,Labels.changedJet]
lemma twists_access (s:Signed) (J:Snap G d): access (twists s.ortho J) = pulling (access J) s 0 := by
  funext e
  apply G.colorMat_injective
  let P:= fun A:Snap G d=> (hol G).links d (expand d A) 1
  have he := (Work.G02.linkGerm (hol G) d e).2.2 (twists s.ortho J)
  simp_rw [twists_links, pull] at he
  apply he.unique; unfold pulling pull Step.read
  split_ifs
  · simp only [G.mat_inv, Function.comp_apply]; change HasDerivAt _ (G.colorMat (-access J _)) _; rw [map_neg,← G.colorMat_skew]; exact ((Work.G02.linkGerm (hol G) d _).2.2 J).star
  exact (Work.G02.linkGerm (hol G) d _).2.2 J

def choiceW (G : Gauge) (d : ℕ) := (Normal.milk (WickK G)).comp (letters G d)
def writeW (G : Gauge) (d : ℕ):= (MvPolynomial.rename (Subtype.val : KeyIn G d→Labels.Key G)).toLinearMap.comp ((Pi0 G d).comp (choiceW G d))

lemma off_e (J:Snap G d) (p:poly (AKey G)) : aeval (kp d J) (off G d p)=text (curlC G (access J)) p := by
  apply DFunLike.congr_fun (f:=(aeval _).comp (off G d)); ext1 i; simp only [AlgHom.comp_apply, aeval_X]; exact off_X ..
lemma off_seed (v : (Frame G d).Coeff) (J : Snap G d): aeval (kp d J) (off G d (choiceW G d v))= local_heat G (letters G d v) (access J) := by rw [off_e]; rfl
lemma canon_read (v : (Frame G d).Coeff) (J : Labels.Jet G): Labels.read J (writeW G d v)= evaluate_ray (fun t=>local_heat G (letters G d v) (access (flash (Drops.trunk d J) t))) d := by
  let p:= Pi0 G d (choiceW G d v)
  rw [show writeW G d v= (rename (Subtype.val : KeyIn G d→Labels.Key G) p) from rfl]
  have he: Labels.read J (rename (Subtype.val : KeyIn G d→Labels.Key G) p)= aeval (kp d (Drops.trunk d J)) p:= by
    apply DFunLike.congr_fun (f:=(Labels.read J).comp (rename (Subtype.val : KeyIn G d→Labels.Key G))); ext1 i
    have h : i.val.1<d-1 := (spanKey d i).isLt
    simp only [AlgHom.comp_apply, Labels.read,kp,Labels.coord,expand,Drops.trunk,dif_pos h,rename_X,aeval_X]
  rw [he,Pi0_read]; simp_rw [off_seed]

lemma withinW (v:(Frame G d).Coeff): writeW G d v∈ Labels.localFields G d := by
  let p:= Pi0 G d (choiceW G d v); let X:= writeW G d v
  let f:= (Subtype.val : KeyIn G d→Labels.Key G)
  constructor
  · have hp : Rise.trim X Labels.generation d=X := by
      change Rise.trim (rename f p) _ _=rename f p; rw [trim_rename]
      have hu : Rise.trim p (key G d) d=p := by
        change Rise.trim (Rise.trim (off G d _) _ _) _ _=Rise.trim ..
        ext1 i; simp only [Rise.trim_coeff]; split_ifs <;> simp
      rw [show Labels.generation∘f=key G d from rfl, hu]
    intro i hi
    change Finsupp.weight Labels.generation i≤d
    change i∈X.support at hi
    by_contra H; rw [← hp] at hi; exact (mem_support_iff.mp hi) (Rise.trim_coeff .. |>.trans (if_neg H))
  intro J u; rw [canon_read,canon_read]; apply congr_arg (fun P => evaluate_ray P d)
  funext t
  let Z:= flash (Drops.trunk d J) t; let A := access Z; let P:= letters G d v
  have ht : flash (Drops.trunk d (Labels.colored u J)) t=Cast u Z := by
    funext i; dsimp only [flash,Drops.trunk,scaleJet,Cast,Z, Labels.colored]; simp [expand,i.isLt]; rfl
  have he : ∀ A:CoverC G, text (curlC G A) (exchange (colorM G u) P)=text (curlC G A) P := by
    intro A; unfold text; rw [Normal.reads_val, reads_color]; exact color_letters ..
  rw [ht, colors_access]
  change local_heat G P (colorPull G u A)=_
  calc
    _=local_heat G (exchange (colorM G u) P) A:= by unfold local_heat; rw [Normal.wets,cov_color,reads_color]
    _=_:= heat_congr G _ _ he A

def LabelW (G : Gauge) (d:ℕ) := (writeW G d).codRestrict (Labels.localFields G d) withinW
def W0 (G : Gauge) (d:ℕ):= (Frame G d).coords.toLinearMap.comp (LabelW G d)

lemma starsW (v : (Frame G d).Coeff): LabelW G d (star v)=Labels.realBar (LabelW G d v) := by
  apply Subtype.ext; change writeW G d _ = Labels.conjPol (writeW G d _); apply Labels.eval_ext; intro J
  rw [Labels.conj_value,canon_read,canon_read]; let p:= letters G d v
  have hp : ∀ A:CoverC G, local_heat G (letters G d (star v)) A=star (local_heat G p A):= by
    intro A; rw [heat_congr G _ (retro _ p) (fun A=> by rw [escorted]; exact star_letters ..)]; unfold local_heat; rw [Normal.blend_components,Normal.blend_components,Spindle.flashed (WickK G) (real_WickK G) p]; exact escorted ..
  simp_rw [hp]
  unfold evaluate_ray p; rw [star_sum]
  refine Finset.sum_congr rfl fun k _=> ?_
  rw [← show ∀ f:ℝ→ℂ,star f=fun x=>star (f x) from fun _=>rfl,iterated_star]; simp -- inspect
lemma W0_real (v : (Frame G d).Coeff): W0 G d (star v)=star (W0 G d v):= by
  let F:=Frame G d; let P:= LabelW G d v; funext i
  change F.coords (LabelW G d (star v)) i=star (F.coords P i)
  rw [starsW]; simpa only [Labels.Frame.conj_basis,LinearEquiv.symm_apply_apply,P] using F.conj_basis (F.coords P) i

set_option maxHeartbeats 400000 in
lemma spinsW (s:Signed) (v : (Frame G d).Coeff) : LabelW G d ((Frame G d).act s.ortho v)=Labels.tensor s.ortho (LabelW G d v) := by
  apply Subtype.ext; change writeW G d _=Labels.rotated s.ortho (writeW G d _); apply Labels.eval_ext; intro J
  rw [Labels.rotated,Labels.eval_changed,canon_read,canon_read]; apply congr_arg (fun P=> evaluate_ray P d); funext t
  let Z:=flash (Drops.trunk d J) t; let A:= access Z; let p:= letters G d v
  have he: ∀ A:CoverC G,text (curlC G A) (letters G d ((Frame G d).act s.ortho v))= text (curlC G A) (exchange (signedM G s) p) := by intro A; unfold text; rw [Normal.reads_val, reads_spin]; exact (signed_letters ..).symm
  have hg : flash (Drops.trunk d (Labels.changedJet (fun i => Labels.Taylor.turn s.ortho⁻¹) J)) t=twists s.ortho Z := (twists_flash s.ortho _ t).symm
  rw [hg, twists_access, heat_congr G _ _ he]; unfold local_heat; rw [Normal.wets,spins_cov, reads_spin]

lemma W0_H (s:Signed) (v:(Frame G d).Coeff): W0 G d ((Frame G d).act s.ortho v)=(Frame G d).act s.ortho (W0 G d v) := by
  change (Frame G d).coords (LabelW G d _)= _
  rw [spinsW]; exact (Labels.Frame.act_coords ..).symm
end YM.XSpace
