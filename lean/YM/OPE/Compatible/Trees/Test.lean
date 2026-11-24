import YM.OPE.Compatible.Trees.Budget

/-!
# Uniform estimates and tested scope

Constants do not use lower bounds on ratios. `Grounds` includes the point
hypotheses for all projections used in that nested expression, so can
consume also with continuity-on-separated geometry. Point exteriors also
vary freely with fixed positive clearance, retaining measures as in
`YM.OPE.Compatible.Joint`. For each set of fixed radii (or separately
pointwise first) integrate also against arbitrary bounded-mass profiles in
compact permitted exterior, center and vertex configurations (those include
the continuous rescalings in scale-shape tests). There's no positive floor
on *what* child scale can be chosen before that test; the mass gets the
same loss budget. As usual to use variable radii inside an estimate, the
RHS also changes pointwise, not claiming a geometry-independent bounded-mass
test price through configurations approaching collision at an actual zero
ratio.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter MeasureTheory Cov Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type}[PartialOrder V][OrderBot V][Fintype V](E:Origin V)
    {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
    {J:Type}[Fintype J] (p:V→ S.Tag)(D:V→ℕ)(a:Tones U)

/-- usable domain simultaneously on all valid cuts incl intermediate
replacements, component functions refer to the same `beam` coefficients -/
def Fresh (S:Table C.book)(s:V→ ℝ)(x:V→ E4): Prop:= ∀ (P:Finset V), Crown P →
  ∀ v∈ P, Covered S (s v) (picked (glen E P v) x) (x v)
lemma fresh_direct {s:V→ℝ}{x:V→E4} (h:Fresh E S s x)(P:Finset V)(hp:Crown P) :
    Covered S (s ⊥) (picked (brim E P) x) (x ⊥):=by
  have he:= h P hp ⊥ hp.base; rwa [glen_bot] at he

/-- Bundle of point statements with the arbitrary cuts simultaneously
fitting (for consumption by any of the symmetry/joint consumers). -/
structure Grounds (ε:ℝ) (q:J→ S.Tag)(n:ℕ) (s:V→ ℝ)(x:V→ E4)(y:J→ E4) : Prop where
  ready : Fresh E S s x
  price : ‖frontierCoefficient E U (heart V) a s x p‖ ≤ fuel E p ε a.fst s
  seen : Seen U n (s ⊥) (picked (brim E (heart V)) x) (picked (brim E (heart V)) p)
    (x ⊥) y q (fuel E p ε (n+1:ℝ) s)
  error : ‖frontierCoefficient E U (heart V) a s x p - nests E U D (heart V) a s x p‖ ≤
    fuel E p ε a.fst s*plugs E D s

variable (Z : Services C F S) {M η ε c : ℝ} (h0:⊥∈ heart V) (hM:0≤M) (hη:0<η) (hε:0<ε)
  (hc:0<c)(q:J→ S.Tag)(n:ℕ)
include h0 hM hη hε hc Z
lemma ground_price : ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ (s:V→ℝ)(x:V→E4), Layout E M η s x → s ⊥=r →
    ∀ y:J→ E4, ClearOf (x ⊥) y c → Grounds E U p D a ε q n s x y := by
  let Q (r:ℝ) (i:(V→ℝ)× (V→ E4) × (J→ E4)) := Layout E M η i.1 i.2.1 ∧ i.1 ⊥=r ∧ ClearOf (i.2.1 ⊥) i.2.2 c
  have he : ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ i, Q r i → Grounds E U p D a ε q n i.1 i.2.1 i.2.2:= by
    apply refine_geometry
    intro f ψ hN hu h
    obtain ⟨φ,hφ,hw,T,t,L⟩ := refinement (S:=fun r=> (f r).1) (X:=fun r=> (f r).2.1) E h0 hM hη
      (h.mono fun _ hi=> hi.1) ((tendsto_id.mono_left hu).congr' (h.mono fun i hi=> hi.2.1.symm))
    refine ⟨φ,hφ,hw,?_⟩
    have hf : ∀ᶠ i in φ, Fresh E S (f i).1 (f i).2.1 := eventually_all.mpr fun P => eventually_all.mpr
      fun h:Crown P => eventually_all.mpr fun v=> eventually_all.mpr fun hv=> L.live E P h S (v:=v) hv
    filter_upwards [hf,coeff_price E U L p Z hε a,nested_price E U L p D Z hε a,seen_price (Y:=fun i=> (f i).2.2)
      E U L p Z hε q n hc ((h.filter_mono hw).mono fun _ hi=> hi.2.2)] with i hi hp he hw using ⟨hi,hp,hw,he⟩
  filter_upwards [he] with r he s x hx hr y hy
  exact he (s,x,y) ⟨hx,hr,hy⟩

omit hM hη hε hc Z
section geometry
variable {B:Type}[TopologicalSpace B] (P:Finset V)(H:Crown P) (x:B→ V→ E4)(s:V→ℝ)(hx:Continuous x)
    (h : ∀ b, Fresh E S s (x b))
omit h0 [PartialOrder V] [OrderBot V] [Fintype V] in
lemma x_continuous (Q:Finset V) (hx:Continuous x) : Continuous (fun i=>picked Q (x i)) := continuous_pi fun j=>
  (continuous_pi_iff.mp hx) j.val
include H hx h
omit h0 in
lemma shoot_continuous {v:V}(hv:v∈P) : Continuous (fun i=>shoot E U P v a s (x i) p) :=
  continuous_iff_continuousAt.mpr fun b=> (beamSmooth U (picked _ p) (x b v) (h b P H v hv) a).continuousAt.comp
    (f:=fun i=>(s v,picked (glen E P v) (x i),x i v)) (continuous_const.prodMk
      ((x_continuous x _ hx).prodMk ((continuous_pi_iff.mp hx) v))).continuousAt
omit h0 in
lemma direct_continuous : Continuous (fun i=>frontierCoefficient E U P a s (x i) p) := by
  simp_rw [direct_bot]; exact shoot_continuous E U p a P H x s hx h H.base
omit h0 in
lemma nested_continuous : Continuous (fun i=>nests E U D P a s (x i) p) := by
  revert H p; apply Finset.lt_wf.induction P
  intro P ih p H
  by_cases hp : (rest P).Nonempty
  · conv => arg 1; ext i; rw [nests,dif_pos hp]
    exact continuous_finsetSum _ (fun b hb=> (shoot_continuous E U p b P H x s hx h (bud_live ..)).mul
      (ih _ (lighter _ (bud_live _ hp)) (paint U (bud P hp) p b) (remains P H (bud_trunk P hp))))
  conv => arg 1; ext i; rw [nests,dif_neg hp]
  exact direct_continuous E U p a P H x s hx h
omit H h
variable [CompactSpace B][SecondCountableTopology B][MeasurableSpace B][BorelSpace B]
  (μ:Measure B)(y:B→ J→ E4)(hy:Continuous y) (φ:B→ℂ) (hφ:Integrable φ μ)
  (grounds: ∀ b, Grounds E U p D a ε q n s (x b) (y b))
include h0 hx grounds hφ μ
omit [CompactSpace B] [SecondCountableTopology B] in
/-- joint tests of coefficients and errors. For tested discrepancy consume
with exactly `Display.joint_price`, `Display.through_mix`, etc.
Includes integrability also of nested error. As for all bounds factor is
*just the total mass*, no power loss through the tests even on very small
ratios. -/
lemma joint : let W b:= frontierCoefficient E U (heart V) a s (x b) p
    let z b:= nests E U D (heart V) a s (x b) p
    let u:= fuel E p ε a.fst s
    Integrable (fun b=> φ b*W b) μ ∧
      ‖∫ b,φ b*W b ∂μ‖ ≤ u*(∫ b, ‖φ b‖ ∂μ) ∧
      Integrable (fun b=> φ b*z b) μ ∧
      ‖(∫ b,φ b*W b ∂μ)-(∫ b,φ b*z b ∂μ)‖ ≤ u*plugs E D s*(∫ b, ‖φ b‖ ∂μ) := by
  intro W z u
  have hw : Continuous W := direct_continuous E U p a _ (tall h0) x s hx (fun b=> (grounds b).ready)
  have hz : Continuous z := nested_continuous E U p D a _ (tall h0) x s hx (fun b=> (grounds b).ready)
  obtain ⟨he,hf⟩:= within_price μ φ hw.aestronglyMeasurable hφ (fun b=> (grounds b).price)
  obtain ⟨hg,hj⟩:= within_price μ φ (p:= fun b=> W b-z b) (hw.sub hz).aestronglyMeasurable hφ
    (fun b=> (grounds b).error)
  change Integrable (fun b=> φ b*W b) μ at he
  change Integrable (fun b=> φ b*(W b-z b)) μ at hg
  have ht:Integrable (fun b=>φ b*z b) μ := (he.sub hg).congr (Eventually.of_forall (fun b=> by
    change φ b *W b-φ b*(W b-z b)=_; ring))
  refine ⟨he,hf,ht,?_⟩
  change ‖(∫ b,φ b*(W b-z b) ∂μ)‖ ≤ _ at hj
  simp_rw [mul_sub,integral_sub he ht] at hj; exact hj
end geometry

/-- All epsilon results on trees at one Final and covariant prescription. -/
structure Nested (U:Spec.Final C F S) : Prop where
  budgets {V:Type} [PartialOrder V][OrderBot V][Fintype V] (E:Origin V) (p:V→ S.Tag)(D:V→ ℕ)(a:Tones U)
    (M η c ε:ℝ){J:Type}[Fintype J] (q:J→ S.Tag) (n:ℕ) : ⊥ ∈ heart V → 0 ≤ M → 0<η → 0<c → 0<ε →
      ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ (s:V→ℝ)(x:V→E4), Layout E M η s x → s ⊥=r →
        ∀ y:J→ E4, ClearOf (x ⊥) y c → Grounds E U p D a ε q n s x y
omit h0
include Z
lemma all_trees : Nested U := ⟨fun E p D a _ _ _ _ _ _ q n h0 hM hη hc hε=>
  ground_price E U p D a Z h0 hM hη hε hc q n⟩

omit Z
/-- Endpoint through tree subpower results. Same Spec.Final statement as before. -/
theorem subpower (G:Gauge) (h:G.Simple) : ∃ (C:Family G) (f:Extraction.Order) (S:Table C.book),
    Services C f S ∧ ∃ U : Spec.Final C f S, Display.Simple U ∧ Nested U := by
  obtain ⟨C,g,S,Z,U,h⟩ := Display.slope G h; exact ⟨C,g,S,Z,U,h,all_trees U Z⟩
end YM.OPE.Arboreal
