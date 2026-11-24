import YM.Integration.WilsonOrdinaryNestedBasis

/-! Finite fixed dictionary probes of the full signed output on comparable
shapes suffice at a vertex including its genuine incoming normalization. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedFixedInput
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom OPE.Nesting.Composite
open PhysMS Trace.Pilot RG17 Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater
open FVA2 FVA2.Register FVA2.Scale WilsonCenteredNestedProgram WilsonCenteredNestedGross
open WilsonPositionHomogeneousFrame WilsonOrdinaryNestedMSVertex WilsonOrdinaryNestedLocal
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z



open WilsonOrdinaryNestedBasis
variable {n:ℕ}

def Fixed (U η:ℝ) (p q h:ℕ) (d:Fin n→ℕ) : Prop :=
  ∀c:Choice G d,∃C:ℝ,0≤C ∧ ∀ᶠr:ℝ in trail,∀z:Points n,
   (∀i:Fin n,‖z i‖≤U) → (∀i j:Fin n,i≠j→η≤‖z i-z j‖) →
   ‖gap (Q:=Q) (J:=J) Z M ν d h q r z (axes (R:=R) d c)‖ ≤ C*(θ r)^p

include run in
theorem income (clock:Coupling G θ) (v:Fin n→ S.Tag):
    ∃W:ℕ,∀c:Choice G (degrees v),∃K:ℝ,0≤K ∧ ∀ᶠr:ℝ in trail,
    ‖due (R:=R) (degrees v) (raised F J Z r v) c‖≤K/(θ r)^W :=by
  have state (i:Fin n):=WilsonOrdinaryNestedInput.original run Z clock (v i).1 (v i).2
  choose K l Kp paid using state
  refine ⟨∑i,l i,?_⟩
  intro c
  let L(i:Fin n): Free R.family (degrees v i) →L[ℂ] ℂ :=
    ((WilsonMSDictionaryVector.basis R.family (degrees v i)).coord (c i)).toContinuousLinearMap
  refine ⟨∏i,‖L i‖*K i,Finset.prod_nonneg fun i _=>mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (Kp i),?_⟩
  filter_upwards [Filter.eventually_all.mpr paid] with r wage
  have price(i:Fin n):
      ‖(L i) (raised F J Z r v i)‖≤(‖L i‖*K i)/(θ r)^(l i):=by
    calc
      _ ≤ ‖L i‖*‖raised F J Z r v i‖ := (L i).le_opNorm _
      _ ≤ ‖L i‖*(K i/(θ r)^(l i)):=mul_le_mul_of_nonneg_left (wage i) (ContinuousLinearMap.opNorm_nonneg _)
      _ = _:=by ring
  change ‖∏i,(L i) (raised F J Z r v i)‖≤_
  rw [norm_prod]
  exact (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>price i)).trans_eq (by
    rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum])

theorem placement {U η r:ℝ} (rp:0<r) (x:Fin n→E4) (o:E4)
    (room:∀i,‖x i-o‖≤U*r) (gaps:∀i j,i≠j→η*r≤‖x i-x j‖):
    (∀i,‖placed r x o i‖≤U) ∧ (∀i j,i≠j→η≤‖placed r x o i-placed r x o j‖) := by
  have scale:∀i,r • placed r x o i=x i-o:=WilsonOrdinaryNestedMSVertex.geometry r rp x o
  constructor
  · intro i
    have h:=room i
    rwa [← scale i,norm_smul,Real.norm_eq_abs,abs_of_pos rp,mul_comm U r,mul_le_mul_iff_right₀ rp] at h
  · intro i j ne
    have diff:r • (placed r x o i-placed r x o j)=x i-x j:=by rw [smul_sub,scale,scale];abel
    have h:=gaps i j ne
    rwa [←diff,norm_smul,Real.norm_eq_abs,abs_of_pos rp,mul_comm η r,mul_le_mul_iff_right₀ rp] at h

include run in
theorem original (clock:Coupling G θ) (U η:ℝ) (v:Fin n→S.Tag) :
    ∃ W:ℕ,∀w, W≤w→∀P q h:ℕ, Fixed (Q:=Q) (J:=J) Z M ν U η (P+w) q h (degrees v) →
      WilsonOrdinaryNestedDoses.Vertex (Q:=Q) (J:=J) Z M ν U η P q h v := by
  obtain ⟨W,source⟩:=income run Z clock v
  choose K Kp earned using source
  refine ⟨W,?_⟩
  intro w enough P q h tested
  choose C Cp heard using tested
  let B:=∑c:Choice G (degrees v),K c*C c
  refine ⟨B,Finset.sum_nonneg (fun c _=>mul_nonneg (Kp c) (Cp c)),?_⟩
  filter_upwards [Filter.eventually_all.mpr earned,Filter.eventually_all.mpr heard,clock.positive,
    (clock.conforms simple).eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin] with r credit hear gp g1 rp x o room gaps
  let z:=placed r x o
  let a:=raised F J Z r v
  have pos:0<r:=rp
  obtain ⟨bounded,spaced⟩:=placement pos x o room gaps
  have balance (c:Choice G (degrees v)):
      ‖due (R:=R) (degrees v) a c‖*‖gap (Q:=Q) (J:=J) Z M ν (degrees v) h q r z (axes (R:=R) (degrees v) c)‖
      ≤ (K c*C c)*(θ r)^P :=by
    have high: (θ r)^(P+w)≤(θ r)^(P+W):=pow_le_pow_of_le_one gp.le g1 (Nat.add_le_add_left enough P)
    refine (mul_le_mul (credit c) ((hear c z bounded spaced).trans (mul_le_mul_of_nonneg_left high (Cp c)))
      (norm_nonneg _) (div_nonneg (Kp c) (pow_nonneg gp.le W))).trans_eq ?_
    rw [pow_add]
    field_simp
  rw [show WilsonOrdinaryNestedDoses.fieldGap (Q:=Q) (J:=J) Z M ν h q r x o v =
      gap (Q:=Q) (J:=J) Z M ν (degrees v) h q r z a from (by unfold gap;rw [paid];rfl),
    WilsonOrdinaryNestedBasis.original]
  calc
    _ ≤ ∑c:Choice G (degrees v),‖due (R:=R) (degrees v) a c •
      gap (Q:=Q) (J:=J) Z M ν (degrees v) h q r z (axes (R:=R) (degrees v) c)‖:=norm_sum_le _ _
    _ ≤ ∑c:Choice G (degrees v),(K c*C c)*(θ r)^P:=Finset.sum_le_sum fun c _=>by simpa only [norm_smul] using balance c
    _ = _:=by rw [←Finset.sum_mul]
end YM.Integration.WilsonOrdinaryNestedFixedInput
