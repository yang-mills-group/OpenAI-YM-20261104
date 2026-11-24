import YM.Integration.WilsonMacroscopicExteriorEnvelope
import YM.Integration.WilsonSeparatedContinuousGram

/-! The actual external scalar probe on the entire reference label.
Its norm is paid by the measured unit response of precisely this far
roster, including its complex phase, uniformly at fixed clearance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMacroscopicProbe
open Function Set Filter MeasureTheory Lattice Extraction Table Spec OPE OPE.Orbits OPE.Cards OPE.Nesting
open Next.Rank RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection Trace.Pilot
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {R : Run G} {V : Table R.family.book} {f : Extraction.Order}
variable {E : Type} [Fintype E] {e : E→ℕ}

def observe (F : Final R.family f V) (q : Viewers F) (D : ℕ) (y : E→E4) (w : Labels V e) :
    R.family.label D →L[ℂ] ℂ :=
  ((upon (spectator F q) D 0 y w).comp (V.project D)).toContinuousLinearMap

def bill (F : Final R.family f V) (q : Viewers F) (y : E→E4) (w : Labels V e) : ℝ :=
  1+‖upon (spectator F q) 0 0 y w (V.unit 0)‖

private theorem isolated {y:E→E4} {η:ℝ} (hp:0<η) (hy:ClearOf 0 y η) : Injective (beside (sole (0:E4)) y) := by
  apply beside_distinct.mpr
  refine ⟨injective_of_subsingleton _,?_,?_⟩
  · intro i j eq
    by_contra ne
    have h := hy.spread i j ne
    rw [eq,sub_self,norm_zero] at h
    exact hp.not_ge h
  · intro i j eq
    have h := hy.openSpace j
    change (0:E4)=y j at eq
    rw [←eq,sub_self,norm_zero] at h
    exact hp.not_ge h

private theorem singleton (F : Final R.family f V) (q : Viewers F) (D : ℕ) (y : E→E4) (w : Labels V e)
    {η:ℝ} (hp:0<η) (hy:ClearOf 0 y η) (s : ℝ) (v : V.Field D) :
    whole (spectator F q) (posed s (0 : Points 1)) (fun _ : Fin 1=>v) y w = upon (spectator F q) D 0 y w v := by
  let h : Fin 1 ≃ Unit := Equiv.ofUnique .. 
  have H := whole_perm (S:=V) (spectator F q) h (Equiv.refl E) (x:=sole (0:E4)) (v:=fun _:Unit=>v)
    (y:=y) (w:=w) (spectate F q) (isolated hp hy)
  have atZero : posed s (0:Points 1) = (sole (0:E4)) ∘ h := by funext i;simp [posed,sole]
  rw [atZero]
  exact H

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {z₀ : ℝ}
    (source : FundedOriginalProperties.{u} hG z₀ W) (pace : WilsonWindowReportingPace.Slow R.kit) {H:ℕ} (hH:0<H)
    (F : Final R.family f V) (fac : Facilities R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ→tower V) (lead : Leading F J)
    {A : (Bel R.family.book).Hierarchy} (obey : ∀ d:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) d)
    (D : ℕ) (w : Labels V e) {η:ℝ} (ηp : 0<η) {g:ℝ→ℝ} (hg:Coupling G g) :
    ∃ L : ℝ,0≤L ∧ ∀ y : E→E4, ClearOf 0 y η → ∀ q : Viewers F, ‖observe F q D y w‖ ≤ L*bill F q y w := by
  let K : Set (Points 1) := {0}
  have safe : K⊆conf 1 := by intro x _ _ _ _;exact Subsingleton.elim .. 
  obtain ⟨M,nM,bought⟩ := WilsonMacroscopicExteriorEnvelope.amplitude hG W source pace hH F fac Q J lead obey
    (fun _:Fin 1=>D) w (K:=K) isCompact_singleton safe ηp hg
  obtain ⟨s,available⟩ := bought.exists
  let lift : R.family.label D →L[ℂ] (Bel R.family.book).Field D :=
    ((J s D).symm.toLinearMap.comp (V.project D)).toContinuousLinearMap
  refine ⟨M*‖lift‖,mul_nonneg nM lift.opNorm_nonneg,?_⟩
  intro y hy q
  have nb : 0≤bill F q y w := add_nonneg zero_le_one (norm_nonneg _)
  apply (observe F q D y w).opNorm_le_bound (mul_nonneg (mul_nonneg nM lift.opNorm_nonneg) nb)
  intro z
  have paid := available (0:Points 1) (mem_singleton _) y hy q (fun _:Fin 1=>lift z)
  have converted : (fun _:Fin 1=>J s D (lift z))=(fun _:Fin 1=>V.project D z) :=
    funext fun _=>LinearEquiv.apply_symm_apply .. 
  rw [converted,singleton F q D y w ηp hy] at paid
  have get : ‖observe F q D y w z‖ ≤ M*bill F q y w*‖lift z‖ := by
    change ‖upon (spectator F q) D 0 y w (V.project D z)‖≤M*(1+‖upon (spectator F q) 0 0 y w (V.unit 0)‖)*‖lift z‖
    simpa only [Fin.prod_univ_one] using paid
  exact (get.trans (mul_le_mul_of_nonneg_left (lift.le_opNorm z) (mul_nonneg nM nb))).trans_eq (by ring)

end YM.Integration.WilsonSeparatedMacroscopicProbe
