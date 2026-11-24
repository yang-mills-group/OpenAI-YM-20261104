import YM.Integration.WilsonSeparatedRegisteredExterior
import YM.Integration.WilsonMacroscopicRichRegister

/-! All prescribed smooth rich exterior columns are evaluated
simultaneously on the actual finite retained numerical coefficient.
The matrix here is the original measured physical Gram on precisely the
independently prescribed smooth profile and its normalizing Jacobian. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedRichExteriorBank
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Filter Set MeasureTheory Lattice Extraction Table Spec Climb OPE OPE.Orbits OPE.Cards OPE.Nesting RG12 RG17 SharpGram PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Trace.Pilot Frontier6.Road SharedIntrinsicWilsonGrid IntrinsicWilsonTensor WilsonPhysicalRetainedCluster
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}
variable {I : Type} [Fintype I] {d : I→ℕ} {D:ℕ}

def observed (B:Deck G) (J : ℝ→tower V) (φ : Test 2) {τ:ℝ} (tp:0<τ) (D:ℕ)
    (near:I→E4) (ins:Labels V d) : Glyph B D → ℂ := fun b=>
  let X := WilsonMacroscopicRichRegister.exterior B J φ tp b
  ∫ z,X.test z * whole V near ins (X.offset z) X.labels

private theorem pos_price (X:RG17.External R.family V) : 0≤WilsonMacroscopicSmearedDisplacement.price X :=
  integral_nonneg fun _=>mul_nonneg (norm_nonneg _) (add_nonneg zero_le_one (norm_nonneg _))

def tested (Bank : Retained (d:=d) R D) (F : Final R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ→tower V) (B:Deck G)
    (φ:Test 2) {τ:ℝ} (tp:0<τ) (r:ℝ) (j:ℕ) (x:I → Cover) (s:ℕ×ℕ) (c:ℝ) : Prop :=
  ∀ v:(i:I)→Input R.family (d i),
  let near:=R.family.S.gridPoint j ∘ x
  let a:=V.project D (basket R Bank F Q J v r x s)
  ‖observed B J φ tp D near (Frame.born J r v)-
    (WilsonMacroscopicRichMeasuredGram.bank B F J D φ τ).vecMul (WilsonMacroscopicRichRegister.coords B J (τ:=τ) a)‖ ≤ c*∏ i,‖v i‖

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {z₀:ℝ}
    (source : FundedOriginalProperties.{u} hG z₀ W) (pace : WilsonWindowReportingPace.Slow R.kit) {H:ℕ} (hH:0<H)
    (F : Final R.family f V) (fac : Facilities R.family f V) (anchor:I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Bank : Retained (d:=d) R D, ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→tower V), Leading F J → ∀ A : (Bel R.family.book).Hierarchy,
    (∀ m:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) m) → ∀ (B:Deck G) (φ:Test 2) (τ:ℝ) (tp:0<τ),
    ∀ σ:ℝ,σ<1/32 → ∀ g:ℝ→ℝ,Coupling G g → ∀ k:ℕ,∀ ε:ℝ,0<ε →
    ∀ᶠ r in trail,∀ L:Set (I → Cover),L.Finite →
      (∀ x∈L,Plot R.family (P.b r) (P.middle r) (P.j r) x) → ∀ᶠ s in f.fuse,∀ x∈L,
        tested Bank F Q J B φ tp r (P.j r) x s (ε*g r^k*r^D*r^σ) := by
  obtain ⟨Bank,buy⟩ := WilsonSeparatedRegisteredExterior.original hG W source pace hH F fac anchor P
  refine ⟨Bank,?_⟩
  intro Q J lead A obey B φ τ tp σ cap g hg k ε εp
  let X (b:Glyph B D) := WilsonMacroscopicRichRegister.exterior B J φ tp b
  let price (b:Glyph B D) := WilsonMacroscopicSmearedDisplacement.price (X b)
  let total := ∑ b:Glyph B D,price b
  have nTotal : 0≤total := Finset.sum_nonneg fun b _=>pos_price (X b)
  let ε' := ε/(total+1)
  have ε'p : 0<ε' := div_pos εp (by linarith)
  have allPrices (b:Glyph B D) : ε'*price b ≤ ε := by
    have one : price b≤ total := Finset.single_le_sum (fun j _=>pos_price (X j)) (Finset.mem_univ b)
    calc
      _ ≤ ε'*(total+1) := mul_le_mul_of_nonneg_left (one.trans (le_add_of_nonneg_right zero_le_one)) ε'p.le
      _ = ε := by dsimp [ε'];field_simp [show total+1≠0 by linarith]
  have picked (b:Glyph B D) := buy Q J lead A obey (X b) σ cap g hg k ε' ε'p
  filter_upwards [Filter.eventually_all.mpr picked,length_rate.pos,hg.positive] with r granted rp gp L finite legal
  filter_upwards [Filter.eventually_all.mpr (fun b:Glyph B D=>granted b L finite legal)] with s outputs x hx
  intro v
  let near:=R.family.S.gridPoint (P.j r) ∘ x
  let a:=V.project D (basket R Bank F Q J v r x s)
  let N:=∏ i,‖v i‖
  let c:=g r^k*r^D*r^σ*N
  have positive : 0≤c := mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg gp.le _) (pow_nonneg rp.le _))
    (Real.rpow_nonneg rp.le _)) (Finset.prod_nonneg (fun i _=>norm_nonneg _))
  apply (pi_norm_le_iff_of_nonneg (show 0≤ε*g r^k*r^D*r^σ*N from by
    simpa only [c,mul_assoc,N] using mul_nonneg εp.le positive)).mpr
  intro b
  have bound := (outputs b x hx v).2.2
  change ‖observed B J φ tp D near (Frame.born J r v) b -
    (WilsonMacroscopicRichMeasuredGram.bank B F J D φ τ).vecMul (WilsonMacroscopicRichRegister.coords B J (τ:=τ) a) b‖≤_
  rw [←WilsonMacroscopicRichRegister.read_field B F J φ tp b a]
  apply bound.trans
  calc
    _ = (ε'*price b)*c := by dsimp only [price,c,N];ring
    _ ≤ ε*c := mul_le_mul_of_nonneg_right (allPrices b) positive
    _ = _ := by dsimp [c,N];ring

end YM.Integration.WilsonSeparatedRichExteriorBank
