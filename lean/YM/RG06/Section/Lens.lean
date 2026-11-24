import YM.RG06.Section.Pose
import YM.PertExtension.TopCalibration
/-!
# Leading coupling and classical engineering order, matched at finite d

Do NOT take link t as the spacing variable; after taking least coupling
coefficient of the stencil (l), read its engineering jet through d on
actual integrated chord tests. Reuses the difficult existing result
`Heat.Top.leading_correct` at exactly those tests (one `Slot.walk` choice
per input, a `Pose`, lows and Projects). The result is a right inverse
(and nondegeneracy/estimate) on all **off-shell** labels, not
just on monomial legs, and including the common Frames conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Section
open RG06 Weak Lattice Pert Function RG Source Drops Labels Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Push.CutoffProjectors PertExtension.Heat.Top
variable {G : Gauge}{d m : ℕ}{F : Labels.Frame G d}
local notation "V"=> RG.Slot × G.ColorIndex

def chordLine (J:Labels.Jet G)(r:ℝ) := access (trunk d (Source.scaleJet J r))

lemma issue_written (B:Fin m→RG.Slot)(p:Pose G m)(l :ℕ)(hp:lows p l)(J:Jet G)(r:ℝ): PowerSeries.constantCoeff (issue B p (chordLine (d:=d) J r) l)= symbolEval (d:=d) (rawPart B p l) J r := by
  rw [originValues _ _ _ _ hp]; rfl

def leadingBook (D:SectionData F)(i:F.Index)(A:Lens G d) : ℂ :=
  iteratedDeriv A.2.val (fun r:ℝ=>PowerSeries.constantCoeff (start D (chordLine (d:=d) A.1 r) i)) 0

lemma correct_label {H:Hol G}(D:SectionData F)(h:D.Sound H)(i:F.Index) : Projects H (F.basis i) (D.evaluate (Pi.single i 1)) := by
 rw [← F.coords_basis]
 convert! h.projects (F.coords (F.basis i)); exact (F.coords.symm_apply_apply _).symm

theorem recovery {H:Hol G}(D:SectionData F)(h:D.Sound H)(P:pop D)(i:F.Index)(J:Lens G d): leadingBook D i J = probe F J (Pi.single i 1) := by
  obtain ⟨m,B,_,p,hp,hq⟩:=P i
  unfold leadingBook; simp_rw [sameStart (B:=B) _ hp hq,issue_written (d:=d) B p _ hq]
  exact leading_correct i p B hq (hp ▸ correct_label D h i) J

def envelope (D:SectionData F)(v:F.Coeff)(J:Lens G d)(r:ℝ) := ∑ i:F.Index,v i*PowerSeries.constantCoeff (start D (chordLine (d:=d) J.1 r) i)

lemma swell {D:SectionData F}(P:pop D)(i:F.Index)(J:Jet G): ContDiff ℝ ω (fun r:ℝ=> PowerSeries.constantCoeff (start D (chordLine (d:=d) J r) i)) :=by
  obtain ⟨m,B,_,p,hp,hq⟩:=P i
  simp_rw [sameStart (B:=B) _ hp hq,issue_written (d:=d) B p _ hq]; exact smooth_symbol ..

def profiles (D:SectionData F)(v:F.Coeff)(J:Lens G d) := iteratedDeriv J.2.val (envelope D v J) 0

theorem all_recovers {H:Hol G}(D:SectionData F)(h:D.Sound H)(P:pop D)(v:F.Coeff)(J:Lens G d): profiles D v J=probe F J v:=by
  have hv(i:F.Index):ContDiffAt ℝ (↑(J.2.val:ℕ)) (fun t:ℝ=> v i • PowerSeries.constantCoeff (start D (chordLine (d:=d) J.1 t) i)) 0:= (show ContDiffAt ℝ (↑(J.2.val:ℕ)) _ 0 from (contDiffAt_const (c:=v i)).smul ((swell P i J.1).contDiffAt.of_le le_top))
  unfold profiles envelope; erw [iteratedDeriv_fun_sum (fun i _=> hv i)]
  have hc (f:ℝ→ℂ) (z:ℂ) : iteratedDeriv J.2.val (fun t=>z • f t) 0 = z • iteratedDeriv J.2.val f 0:= iteratedDeriv_const_smul_field z f
  simp_rw [hc, show ∀ i:F.Index,iteratedDeriv J.2.val (fun t:ℝ=> PowerSeries.constantCoeff (start D (chordLine (d:=d) J.1 t) i)) 0=probe F J (Pi.single i 1) from fun i=> recovery D h P i J, ← (probe F J).map_smul, ← _root_.map_sum]; congr 1; funext i; simp [Finset.sum_apply, Pi.single_apply]

/-- Finite Lens detection in the norm on actual F.Coeff (Fintype prod
sup norm), differentiating the *free least term* from every actual
stencil. Constants independent of volume. ONLY at these lenses on the
cover (no wrapping physics assertion). -/
theorem ledger (D:SectionData F){H:Hol G}(h:D.Sound H)(P:pop D) :
    ∃ (I : Finset (Lens G d))(c:ℝ), 0<c ∧ ∀ v:F.Coeff,c*‖v‖≤ ∑ i∈ I,‖profiles D v i‖:=by
  obtain ⟨I,c,hc,he⟩:= probes_bound F; exact ⟨I,c,hc,fun v=> by simpa only [all_recovers D h P] using he v⟩

-- Explicit linear projection of the free leading labels back to coordinates,
-- and measured detection separation. Arbitrary table inversion later.
open PertExtension.Heat

def leadingProject (F:Labels.Frame G d): (Lens G d→ℂ) →ₗ[ℂ] F.Coeff := Top.reconstruct F

theorem project {D:SectionData F}{H:Hol G}(h:D.Sound H)(P:pop D)(v:F.Coeff): leadingProject F (profiles D v)=v:=by
  rw [funext (all_recovers D h P v)]; exact reconstruct_eq ..

theorem sensing {D:SectionData F}{H:Hol G}(h:D.Sound H)(P:pop D){x y:F.Coeff}(he:profiles D x= profiles D y):x=y:= by rw [← project h P x,he,project h P y]
end YM.RG06.Section
