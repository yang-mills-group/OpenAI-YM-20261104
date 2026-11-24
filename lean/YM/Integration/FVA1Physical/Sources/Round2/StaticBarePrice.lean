import YM.Integration.FVA1Physical.Sources.Round2.BasisWilson
import YM.Integration.FVA1Physical.Round2.StageThreshold

/-! The actual one-step mixed physical input is priced before the run and
the torus: only the two block specifications, the group and the bounded
external field enter. Each evaluation uses the original RG02 joint
coefficient and its own full conditional partition function. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Function Set Lattice RG Wilson Precision Tree Marker Comparison.RG02
open FVA2.CityHistory FormalOPE.RG10.InversionTop RGComparison.Core16 RGComparison.Core16.Spool
open RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven Next.Foundations
open PhysicalNext.Repeat.Legato PertExtension.Series.Tested
open YM.Integration.FVA1Physical.Wilson
open scoped Classical BigOperators Topology
variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I] (R : Census I)

/-- The compact-cover field type is fixed before any physical trajectory or choice of anchors. -/
abbrev CoverLabel (G : Gauge) (d : ℕ) := Σ h : Fin (d+1), ((Labels.frames G).level h.val).Index

private def canonicalLamp {d : ℕ} (a : I → CoverLabel G d) (s : R.Mode) (j : s.val) : Lamp G :=
  investment (sound G (a j).1.val) (valuation G (a j).1.val) (a j).2

private def CommonPrice {d : ℕ} (P : Patch) (K : KernelChoices) (a : I → CoverLabel G d)
    (s : R.Mode) (r : ℕ) (Q δ C : ℝ) : Prop :=
  ∀ (A : Run G) (m p : ℕ), let S:=A.family.path.levels.clock.op m p
  S.patch=P → S.kernel=K → ∀ (y : I → Site (A.family.side (m+1) p)) (F : Forest S.ratio)
    (t : S.Choices) (u : Pins G (A.family.side m p)) (L : Bulk.Chain A.family.path),
    Bid.Larger (G:=G) S → (∀ e, ‖u e‖ ≤ Q) → ∀ g, 0<g → g ≤ δ →
    let x:=axesP G _ u
    let U:=placeLabels (C:=A.family) a y
    let v:=fun k=>(MSMatch.SourceTop.datum R m p U F t x).ordinaryCoefficient L r k s
    ‖(MSMatch.SourceTop.torusVacuum (C:=A.family) m p x g)⁻¹ •
      MSMatch.SourceTop.torusFull m p U x s.val g - peval v r g‖ ≤ C*g^(r+1)

private theorem commonPrice {d : ℕ} (P : Patch) (K : KernelChoices) (a : I → CoverLabel G d)
    (s : R.Mode) (r : ℕ) (Q : ℝ) (hQ : 0<Q) :
    ∃ δ C, 0<δ ∧ 0≤C ∧ CommonPrice R P K a s r Q δ C := by
  by_cases h : P.Branches K G
  · obtain ⟨O⟩:=Oven.builtafter P
    obtain ⟨X,hX,ready⟩:=Oven.fund O h Q hQ
    let J:=canonicalLamp R a s
    obtain ⟨B,C,_,hC,offer⟩:=every J ready (⟨1,0,le_rfl⟩:Lumen.Stage) r (chart_ok G)
    refine ⟨Forge.dollar B.L,C,Forge.dollar_pos _,hC,?_⟩
    intro A m p S hP hK y F t u L size hu g hg small x U v
    subst P;subst K
    let positions:=modeSite R U s
    have hold : ∀ e, ‖u e‖ ≤ X.Q := by simpa only [hX] using hu
    have price:=offer (A.family.side m p) (A.family.side (m+1) p) S.sizes size F u positions hold
    have eq (k : ℕ) (hk : k≤r) : v k = rank J S F X (chart G) u positions k :=
      normalized_coefficients R U A.makes (valuation G) u L F t s ready size hold (chart_ok G) hk
    have same : peval v r g = peval (rank J S F X (chart G) u positions) r g :=
      Finset.sum_congr rfl fun k hk => congrArg (fun z:ℂ=>g^k • z) (eq k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    rw [same,sourceRatio_eq_reads R U A.makes (valuation G) u s g]
    exact (price.cost g hg small).trans_eq (mul_comm ..)
  · refine ⟨1,0,zero_lt_one,le_rfl,?_⟩
    intro A m p S hp hk y F t u L size
    exact (h (hp ▸ hk ▸ size.1)).elim

/-- Both the small-coupling interval and its joint Taylor price precede the
choice of running orbit, stage, period, realization of the independent Wilson
prescription, all forest charts and all physical insertions. -/
theorem static_bare_price (d r : ℕ) (Q : ℝ) (hQ : 0<Q) (P : Patch) (K : KernelChoices) :
    ∃ δ C, 0<δ ∧ 0≤C ∧ ∀ (a : I → CoverLabel G d) (s : R.Mode),
      CommonPrice R P K a s r Q δ C := by
  let T:Type:=(I → CoverLabel G d) × R.Mode
  letI : Nonempty (CoverLabel G d):=⟨⟨0,0⟩⟩
  letI : Nonempty R.Mode:=⟨R.quiet⟩
  choose δ C hδ hC offer using fun t:T=>commonPrice R P K t.1 t.2 r Q hQ
  let e:=Finset.univ.inf' Finset.univ_nonempty δ
  refine ⟨e,∑ t:T,C t,(Finset.lt_inf'_iff _).2 (fun t _=>hδ t),Finset.sum_nonneg (fun t _=>hC t),?_⟩
  intro a s A m p S hp hk y F t u L size hu g hg hs x U v
  have hsmall : e≤δ (a,s):=Finset.inf'_le _ (Finset.mem_univ _)
  have hc : C (a,s)≤∑ j:T,C j:=Finset.single_le_sum (fun j _=>hC j) (Finset.mem_univ _)
  exact (offer (a,s) A m p hp hk y F t u L size hu g hg (hs.trans hsmall)).trans
    (mul_le_mul_of_nonneg_right hc (pow_nonneg hg.le _))

end YM.Integration.FVA1Physical.Round2.Curvature
