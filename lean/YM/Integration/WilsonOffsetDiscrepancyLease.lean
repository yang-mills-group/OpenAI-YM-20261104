import YM.Integration.WilsonOffsetPrimaryLease
import YM.Integration.WilsonOffsetReportingProducts
import YM.Integration.WilsonUniformEquationPrice

/-! The signed calibrated replacement at a genuine microscopic position,
tested in any larger physical cell that accommodates the funded stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetDiscrepancyLease
open Function Set Filter Lattice Cells Wilson RG RG16 RG16.Literal Labels Source Push Extraction
open Next.Extract MergeProof PhysicalNext.Repeat.Legato WilsonOffsetEquationLaw WilsonOffsetReportingProducts
open scoped Classical Topology
universe u
variable {G : Gauge} {C : Family G} {d : ℕ}

theorem place (V : SectionData (C.labels.level d)) (N p : ℕ) (P : C.label d ≃ₗ[ℂ] C.label d)
    (z : C.label d) (o : Site (C.side N p)) :
    residual C V N p P z 0 ∘ Lattice.translate o = residual C V N p P z o := by
  funext U
  simp only [WilsonOffsetReportingProducts.residual,incoming,Family.O,TransferData.cylinder,initial,Function.comp_apply,
    Pi.smul_apply,Pi.sub_apply,SectionData.places_trans,zero_add]

theorem purchased (R : Run G) (hG : G.Simple) {D : Campaign R} (walls : Campaign.Pillars R D)
    {ε : ℝ} (props : WilsonLimitConstruction.FundedOriginalProperties.{u} hG ε walls)
    (pace : WilsonWindowReportingPace.Slow R.kit)
    {V : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
    {P : ∀ d, (ℕ×ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d} {b : Presentation R.family}
    (files : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (sale : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) (d : ℕ)
    {L B : ℝ} (hL : 0 < L) (hB : 4 ≤ B) :
    ∃ A : ℕ → ℝ, Monotone A ∧ (∀ k, 1 ≤ A k) ∧
      (∀ δ > 0, ∃ K : ℝ, 1 ≤ K ∧ ∀ k, A k ≤ K*Real.exp (δ*R.family.S.scale k)) ∧
      (∀ q : ℕ, ∀ δ > 0, ∀ᶠ k in atTop,
        (A (k+1)/A k)^q ≤ Real.exp (δ*(R.family.path.levels.clock.coverSize k:ℝ))) ∧
      ∀ᶠ k in atTop, ∀ N, k < N → ∀ p (hp : port R.family L B hL k ≤ N)
        (x : R.family.label d) (j : ℕ) (hj : j ≤ port R.family L B hL k)
        (o : Site (R.family.side N p)) (v : Site (R.family.side j p)),
        let T := center R.family.S p (hj.trans hp) (0 : Site (R.family.side N p))
        o ∈ T.margin v (3*Cells.span R.family.S hp p) →
        ∃ X : Config G (R.family.side N p) → ℂ, Interior (T.chamber 0) X ∧
          R.family.S.a k^d*T.rootTest (R.family.beta N p) X ≤ ‖x‖*A k ∧
          T.copy v X = residual R.family (V d) N p (P d (N,p)) (x-b.step d (N,p) x) o := by
  let C := R.family
  have pos : 0 < B := by linarith
  obtain ⟨A,mon,one,subp,rate,price⟩ := WilsonUniformEquationPrice.issued R hG walls props pace
    files sale d hL hB
  refine ⟨A,mon,one,subp,rate,?_⟩
  filter_upwards [price,WilsonMovingReportFootprint.original C hG (V d).stencil hL pos,
    WilsonMovingReportFootprint.original C hG (C.localSection d).stencil hL pos] with k hk hv ht
  intro N hn p hp x j hj o v T hi
  let y := x-b.step d (N,p) x
  let s := center C.S p hp (0 : Site (C.side N p))
  have native : Interior (s.chamber 0) (C.O N p y 0) :=
    (WilsonSignedEquationColumns.inside (C.localSection d) (R.makes.sections d) 0
      ((C.factory d N p).terminal.symm y)).enlarges (ht N hn.le p hp 0)
  have restored : Interior (s.chamber 0) (incoming C (V d) N p (P d (N,p)) y 0) :=
    (WilsonSignedEquationColumns.inside (V d) (files d).valid 0
      ((P d (N,p)).symm ((C.factory d N p).terminal.symm y))).enlarges (hv N hn.le p hp 0)
  have fit : Interior (s.chamber 0) (residual C (V d) N p (P d (N,p)) y 0) := by
    change Interior _ (fun z => _-_)
    simpa only [sub_eq_add_neg,neg_one_mul] using native.plus (restored.scale (-1 : ℂ))
  have paid := hk N hn p hp x
  have coin : 0 < C.S.a k^d := pow_pos (C.S.a_pos k) d
  have bound : s.rootTest (C.beta N p) (residual C (V d) N p (P d (N,p)) y 0) ≤
      ‖x‖*A k/(C.S.a k^d) := (le_div_iff₀' coin).mpr paid
  obtain ⟨X,hX,pX,actual⟩ := Frontier6.Platform.moved_basis R.makes hp hj v fit bound hi
  exact ⟨X,hX,(le_div_iff₀' coin).mp pX,
    actual.trans (place ..)⟩

end YM.Integration.WilsonOffsetDiscrepancyLease
