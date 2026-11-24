import YM.Integration.ActualStencilJetFloor
import YM.MS.Wilson.Elect

/-! The full old-MS cylinder of the original finite Wilson section.  The
finite port set is exactly the section's existing used edges.  Periodization
may identify ports: the native cylinder transport retains every such term.
Neither the section nor its observable is chosen again for a regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStencilCylinder
open Function Lattice Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Cylinder.Taylor MS.Native
open MS.Native.Sew MS.Native.Chart MS.Native.Studio
open PertExtension.Series
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}

def realEcho (S : SectionData F) (c : F.Coeff)
    (A : Dict06.Wil.Panel S.stencil G) : ℝ := (Dict06.Wil.echo S c A).re

def cylinder (S : SectionData F) (c : F.Coeff) : Dot G Cover :=
  Sew.art (fun i : UsedEdges S.stencil => i.val) (realEcho S c)

def observed (S : SectionData F) (c : F.Coeff) (n : Side)
    (x : Site n) (U : Config G n) : ℝ := (S.places c x U).re

theorem realEcho_analytic (S : SectionData F) (c : F.Coeff) :
    ContDiff ℝ ω (realEcho S c) :=
  Complex.reCLM.contDiff.comp (Dict06.Wil.echo_smooth S c)

theorem observed_continuous (S : SectionData F) (c : F.Coeff)
    (n : Side) (x : Site n) : Continuous (observed S c n x) :=
  Complex.continuous_re.comp (S.continuous_places c x)

def ports (S : SectionData F) (n : Side) (x : Cover) :
    UsedEdges S.stencil → Edge (Site n) :=
  fun i => (wrap n (x + i.val.1), i.val.2)

theorem observed_chart (S : SectionData F) (c : F.Coeff)
    (n : Side) (x : Cover) :
    observed S c n (wrap n x) ∘ nation =
      realEcho S c ∘ Sew.pull (ports S n x) := by
  funext A
  dsimp only [comp_apply]
  unfold observed realEcho SectionData.places SectionData.evaluate
    Dict06.Wil.echo
  apply congrArg Complex.re
  change MvPolynomial.eval (Source.entry (expandAt (wrap n x) (nation A)))
      (S.evalC c) = _
  apply congrArg (fun a : Source.Index G S.stencil → ℂ =>
    MvPolynomial.eval a (S.evalC c))
  funext i
  simp only [Source.entry, Dict06.Wil.lit, Dict06.Wil.flag_eval,
    nation, expandAt, Sew.pulled, ports, comp_apply, map_add, add_comm]

theorem reads (S : SectionData F) (c : F.Coeff) (n : Side)
    (x : Cover) :
    Reads (shown n (Lab.Shift x (cylinder S c)))
      (observed S c n (wrap n x)) := by
  have he := observed_chart S c n x
  have hf : germ (realEcho S c) := (realEcho_analytic S c).contDiffAt
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hf.comp 0 (Sew.pull (ports S n x)).contDiff.contDiffAt
  · rw [shown, Lab.Shift, cylinder, Sew.map_sec, Sew.map_sec,
      Sew.pooled _ hf, he]
    rfl

theorem phase (S : SectionData F) (c : F.Coeff) :
    Tuned (cylinder S c) 0 :=
  Tune_port _ _ (realEcho_analytic S c).contDiffAt

private def extend (S : SectionData F) (A : Dict06.Wil.Panel S.stencil G) :
    Links ℤ G.Color := fun e =>
  if h : e.1 ∈ S.stencil ∧ e.1 + step e.2 ∈ S.stencil then A ⟨e, h⟩ else 0

private theorem restrict_extend (S : SectionData F)
    (A : Dict06.Wil.Panel S.stencil G) :
    Dict06.Wil.restrictLog S.stencil (extend S A) = A := by
  funext i
  exact dif_pos i.property

theorem radial_low (S : SectionData F) (hV : Bid.pop S) (i : F.Index)
    (k : ℕ) (hk : k < (F.grades i).2)
    (A : Dict06.Wil.Panel S.stencil G) :
    Radial.jet (realEcho S (Pi.single i 1)) k A = 0 := by
  let f : ℝ → ℂ := fun t => Dict06.Wil.echo S (Pi.single i 1) (t • A)
  have hf : ContDiff ℝ ω f :=
    (Dict06.Wil.echo_smooth S (Pi.single i 1)).comp
      (contDiff_id.smul contDiff_const)
  have hz : Dict06.Series.ordinary k f = 0 := by
    have hb := congrArg (PowerSeries.coeff k)
      (Dict06.Wil.echo_book S (Pi.single i 1) (extend S A))
    simp only [Dict06.Series.ps_at, Dict06.Wil.echo_exact,
      restrict_extend] at hb
    exact hb.trans (Dict06.Wil.no_lower S hV i k hk (extend S A))
  rw [Radial.homogeneous_derivative _ A k
    ((realEcho_analytic S (Pi.single i 1)).contDiffAt.of_le le_top)]
  change Dict06.Series.ordinary k (Complex.reCLM ∘ f) = 0
  rw [Dict06.Series.ordinary_map f k (hf.contDiffAt.of_le le_top)
    Complex.reCLM, hz, map_zero]

private theorem from_shade {A B : Type*} {h : ℤ}
    (U : Cyl A ℂ) (hU : MS.Book.From U.val h) (T : B → A → ℂ) :
    MS.Book.From (shade T U) h := by
  intro l hl
  rw [← MS.Book.enough (F := shade T U) l rfl, ← MS.Book.mod_ink]
  have hz : MS.Book.model l.length U = 0 := by
    apply Subtype.ext
    ext k
    change MS.Book.mask _ _ k = 0
    by_cases hk : (k.length : ℤ) = l.length
    · rw [MS.Book.enough k hk]
      exact hU k (by omega)
    exact MS.Book.strange k hk
  rw [hz, map_zero]
  rfl

theorem low (S : SectionData F) (hV : Bid.pop S) (i : F.Index) :
    MS.Book.From (cylinder S (Pi.single i 1)).val ((F.grades i).2 : ℤ) := by
  apply from_shade
  exact ActualStencilJetFloor.ink_from_radial _
    (realEcho_analytic S (Pi.single i 1)).contDiffAt _
    (radial_low S hV i)

theorem invariant (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (c : F.Coeff) (n : Side) (x : Site n) :
    OpenGauge (drive n) (observed S c n x) := by
  apply when_invariant
  intro g U
  exact congrArg Complex.re (S.placed_invariant hS x c g U)

/-- The real cylinder is exactly the original basis field, rather than a
new real-part prescription: the selected section supplies its reality. -/
theorem observed_complex (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (i : F.Index) (n : Side) (x : Site n) (U : Config G n) :
    (observed S (Pi.single i 1) n x U : ℂ) =
      S.places (Pi.single i 1) x U := by
  have hb : star (Pi.single i (1 : ℂ) : F.Coeff) = Pi.single i 1 := by
    funext j
    simp only [Pi.star_apply, Pi.single_apply]
    split_ifs <;> simp
  have hr := hS.ordinary_real (Pi.single i 1) (expandAt x U)
  rw [hb] at hr
  have hi := congrArg Complex.im hr
  change (S.places (Pi.single i 1) x U).im =
    -(S.places (Pi.single i 1) x U).im at hi
  apply Complex.ext
  · rfl
  change 0 = (S.places (Pi.single i 1) x U).im
  linarith

theorem section_expansion (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (c : F.Coeff) (n : Side) (x : Site n) (U : Config G n) :
    S.places c x U =
      ∑ i, c i * (observed S (Pi.single i 1) n x U : ℂ) := by
  let L : F.Coeff →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval (Source.entry (expandAt x U))).toLinearMap.comp S.evalC
  have hc : c = ∑ i, c i • (Pi.single i 1 : F.Coeff) := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  change L c = _
  conv_lhs => rw [hc, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change c i * S.places (Pi.single i 1) x U = _
  rw [observed_complex S hS i n x U]

/-- All actual calibration and engineering factors remain explicit on
the original fixed section basis. -/
theorem physical_expansion (C : Family G) (hC : C.Makes) (N p d : ℕ)
    (v : C.label d) (x : Site (C.side N p)) (U : Config G (C.side N p)) :
    C.O N p v x U = Dict06.Actual.factor C N d *
      ∑ i, Dict06.Actual.matrix C N p d v i *
        (observed (C.localSection d) (Pi.single i 1) (C.side N p) x U : ℂ) := by
  rw [Dict06.Actual.names]
  congr 1
  exact section_expansion _ (hC.sections d) _ _ _ _

theorem original_ready (C : Family G) (hC : C.Makes) (d : ℕ)
    (hV : Bid.pop (C.localSection d)) (i : (C.labels.level d).Index) :
    (∀ (n : Side) (x : Site n),
      Continuous (observed (C.localSection d) (Pi.single i 1) n x)) ∧
    (∀ (n : Side) (x : Cover),
      Reads (shown n (Lab.Shift x (cylinder (C.localSection d) (Pi.single i 1))))
        (observed (C.localSection d) (Pi.single i 1) n (wrap n x))) ∧
    (∀ (n : Side) (x : Site n),
      OpenGauge (drive n) (observed (C.localSection d) (Pi.single i 1) n x)) ∧
    MS.Book.From (cylinder (C.localSection d) (Pi.single i 1)).val
      (((C.labels.level d).grades i).2 : ℤ) ∧
    Tuned (cylinder (C.localSection d) (Pi.single i 1)) 0 := by
  exact ⟨observed_continuous _ _, reads _ _, invariant _ (hC.sections d) _,
    low _ hV i, phase _ _⟩

end YM.Integration.ActualStencilCylinder
