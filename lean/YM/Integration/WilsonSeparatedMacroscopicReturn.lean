import YM.Integration.WilsonSeparatedMacroscopicProbe
import YM.Integration.WilsonSeparatedPlottedExterior
import YM.Integration.WilsonSeparatedRosterTerminal

/-! Entire signed physical correlation against a genuinely separated
macroscopic detector versus its scalar evaluation of the actual finite
retained coefficient. The nonlinear cell capture, the exterior tester,
and the cutoff all belong to the same original Wilson family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMacroscopicReturn
open Function Filter Set MeasureTheory Lattice Extraction Table Spec OPE OPE.Orbits OPE.Cards OPE.Nesting
open Next.Rank RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Trace.Pilot Frontier6.Road SharedIntrinsicWilsonGrid IntrinsicWilsonTensor WilsonPhysicalRetainedCluster
open WilsonSeparatedMacroscopicProbe
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}
variable {I E : Type} [Fintype I] [Fintype E] {d : I→ℕ} {e : E→ℕ} {D:ℕ}

def priced (Bank : Retained (d:=d) R D) (F : Final R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ→tower V)
    (r : ℝ) (j : ℕ) (x:I → Cover) (s:ℕ×ℕ) (w : Labels V e) (η c:ℝ) : Prop :=
  let near := R.family.S.gridPoint j ∘ x
  ∀ y : E→E4,ClearOf 0 y η → Injective (beside near y) → ∀ q : Viewers F,q=none ∨ Screen near →
  ∀ v : (i:I)→Input R.family (d i),
    ‖whole (spectator F q) near (Frame.born J r v) y w-observe F q D y w (basket R Bank F Q J v r x s)‖ ≤
      c*bill F q y w*∏ i,‖v i‖

private theorem purchase {g : ℝ→ℝ} (hG:G.Simple) (hg:Coupling G g) (D:ℕ) (σ L:ℝ) (k:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ r in trail,L*Real.exp (-((D:ℝ)+σ+1)*LogV r)≤ε*g r^k*r^D*r^σ := by
  filter_upwards [subpower_payment hg hG L 1 zero_lt_one ε ep k,length_rate.pos] with r fee rp
  change 0<r at rp
  have h : Real.exp (-((D:ℝ)+σ+1)*LogV r)=r^((D:ℝ)+σ+1) := by
    rw [Real.rpow_def_of_pos rp,LogV,Real.log_inv];congr 1;ring
  have pow : r^((D:ℝ)+σ+1) = r^(1:ℝ)*r^D*r^σ := by
    rw [←Real.rpow_natCast,←Real.rpow_add rp,←Real.rpow_add rp];congr 1;ring
  rw [h,pow]
  calc
    _ = L*r^(1:ℝ)*r^D*r^σ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right fee (pow_nonneg rp.le _)) (Real.rpow_nonneg rp.le _)

theorem refinements {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {z₀ : ℝ}
    (source : FundedOriginalProperties.{u} hG z₀ W) (pace : WilsonWindowReportingPace.Slow R.kit) {H:ℕ} (hH:0<H)
    (F : Final R.family f V) (fac : Facilities R.family f V) (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Bank : Retained (d:=d) R D, ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→tower V),Leading F J → ∀ A : (Bel R.family.book).Hierarchy,
    (∀ m:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) m) → ∀ (E:Type) [Fintype E] (e:E→ℕ) (w:Labels V e),∀ η:ℝ,0<η →
    ∀ σ:ℝ,σ<1/32 → ∀ g:ℝ→ℝ,Coupling G g → ∀ k:ℕ,∀ ε:ℝ,0<ε →
    ∀ᶠ r in trail,∀ U:Ultrafilter (ℕ×ℕ),U.toFilter≤f.fuse → ∀ L:Set (I → Cover),L.Finite →
      (∀ x∈L,Plot R.family (P.b r) (P.middle r) (P.j r) x) → ∀ᶠ s in U.toFilter,∀ x∈L,
      priced Bank F Q J r (P.j r) x s w η (ε*g r^k*r^D*r^σ) := by
  obtain ⟨Bank,buy⟩ := WilsonSeparatedRosterTerminal.purchased R hG F fac anchor P
  refine ⟨Bank,?_⟩
  intro Q J lead A obey E _ e w η ηp σ cap g hg k ε εp
  let funds (i:E) := ‖V.representative _ (w i)‖+1
  have nfund (i:E) : 0<funds i := by dsimp [funds];positivity
  have fund (i:E) : ‖V.representative _ (w i)‖≤funds i := le_add_of_nonneg_right zero_le_one
  have measured := WilsonSeparatedPlottedExterior.original F fac anchor Q P J lead hg e funds nfund ηp cap k (half_pos εp)
  obtain ⟨C,nC,detector⟩ := WilsonSeparatedMacroscopicProbe.original hG W source pace hH F fac Q J lead obey D w ηp hg
  let depth:ℝ := (D:ℝ)+σ+1
  filter_upwards [buy Q J lead depth,measured,purchase hG hg D σ C k (half_pos εp),length_rate.pos,hg.positive]
    with r cluster received gate rp gp U sub L finite plotted
  change 0<r at rp
  obtain ⟨Z,same,terminal⟩ := cluster U sub
  filter_upwards [terminal L finite plotted] with s returned x hx
  let near:=R.family.S.gridPoint (P.j r) ∘ x
  intro y clear joined q phase v
  let N:=∏ i,‖v i‖
  let h:=ε/2*g r^k*r^D*r^σ
  let B:=bill F q y w
  let p:=observe F q D y w
  have positiveB : 1≤B := le_add_of_nonneg_right (norm_nonneg _)
  have positiveN : 0≤N := Finset.prod_nonneg fun i _=>norm_nonneg _
  have positiveH : 0≤h := mul_nonneg (mul_nonneg (mul_nonneg (half_pos εp).le (pow_nonneg gp.le _)) (pow_nonneg rp.le _)) (Real.rpow_nonneg rp.le _)
  have physical := received x (plotted x hx) (Z x) ((same x (plotted x hx)).common sub) y clear joined w fund q phase v
  have field : ‖p (Z x v)-p (basket R Bank F Q J v r x s)‖ ≤ h*B*N := by
    rw [←map_sub]
    calc
      _ ≤ ‖p‖*‖Z x v-basket R Bank F Q J v r x s‖ := p.le_opNorm _
      _ ≤ (C*B)*(Real.exp (-depth*LogV r)*N) := by
        rw [norm_sub_rev]
        exact mul_le_mul (detector y clear q) (returned x hx v) (norm_nonneg _) (mul_nonneg nC (zero_le_one.trans positiveB))
      _ = (C*Real.exp (-depth*LogV r))*B*N := by ring
      _ ≤ h*B*N := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right gate (zero_le_one.trans positiveB)) positiveN
  have nearPrice : ‖whole (spectator F q) near (Frame.born J r v) y w-p (Z x v)‖ ≤ h*B*N :=
    physical.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right positiveH positiveB) positiveN)
  exact ((norm_sub_le_norm_sub_add_norm_sub _ (p (Z x v)) _).trans (add_le_add nearPrice field)).trans_eq
    (by dsimp only [N,h,B];ring)

private theorem full_filter {α:Type*} (L:Filter α) (p : α→Prop) (h : ∀ U : Ultrafilter α,U.toFilter≤L → ∀ᶠ x in U.toFilter,p x) :
    ∀ᶠ x in L,p x := Filter.mem_iff_ultrafilter.mpr h

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {z₀ : ℝ}
    (source : FundedOriginalProperties.{u} hG z₀ W) (pace : WilsonWindowReportingPace.Slow R.kit) {H:ℕ} (hH:0<H)
    (F : Final R.family f V) (fac : Facilities R.family f V) (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Bank : Retained (d:=d) R D, ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→tower V),Leading F J → ∀ A : (Bel R.family.book).Hierarchy,
    (∀ m:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) m) → ∀ (E:Type) [Fintype E] (e:E→ℕ) (w:Labels V e),∀ η:ℝ,0<η →
    ∀ σ:ℝ,σ<1/32 → ∀ g:ℝ→ℝ,Coupling G g → ∀ k:ℕ,∀ ε:ℝ,0<ε →
    ∀ᶠ r in trail,∀ L:Set (I → Cover),L.Finite →
      (∀ x∈L,Plot R.family (P.b r) (P.middle r) (P.j r) x) → ∀ᶠ s in f.fuse,∀ x∈L,
      priced Bank F Q J r (P.j r) x s w η (ε*g r^k*r^D*r^σ) := by
  obtain ⟨Bank,buy⟩ := refinements hG W source pace hH F fac anchor P
  refine ⟨Bank,?_⟩
  intro Q J lead A obey E _ e w η ηp σ cap g hg k ε εp
  filter_upwards [buy Q J lead A obey E e w η ηp σ cap g hg k ε εp] with r ready L finite plot
  exact full_filter f.fuse _ (fun U sub=>ready U sub L finite plot)

end YM.Integration.WilsonSeparatedMacroscopicReturn
