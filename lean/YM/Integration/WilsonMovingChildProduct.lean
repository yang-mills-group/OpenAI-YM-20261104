import YM.Integration.WilsonMovingChildLease
import YM.Cells.Embedded

/-! The complete physical signed product on independently occupied cells.
The catalogue of grades and radii is paid before any occurrence is placed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingChildProduct
open Function Set Filter Lattice Cells Wilson RG RG16 RG16.Literal Labels Source Push Extraction
open Next.Extract MergeProof PhysicalNext.Repeat.Legato WilsonOffsetReportingProducts
open scoped Classical Topology BigOperators
universe u v v'
variable {G : Gauge}

theorem placed {J : Type v'} [Fintype J] {n : Side} (T : Tiling n) {β : ℝ} (seam : Seam G n β)
    (o : J → T.Cell) (inj : Injective o) (A : J → Config G n → ℂ) (w M : J → ℝ) (hn : ∀ i, 0 ≤ w i)
    (funded : ∀ i, ∃ X : Config G n → ℂ, Interior (T.chamber 0) X ∧ w i*T.rootTest β X ≤ M i ∧
      T.copy (o i) X = A i) :
    (∏ i, w i)*‖moment β (fun U => ∏ i, A i U)‖ ≤ ∏ i, M i := by
  choose X ix px eq using funded
  have full : (fun U => ∏ i, A i U) = (fun U => ∏ i, T.copy (o i) (X i) U) := by
    funext U; exact Finset.prod_congr rfl fun i _ => congrFun (eq i).symm U
  rw [full]
  calc
    _ ≤ (∏ i, w i)*(∏ i, T.rootTest β (X i)) :=
      mul_le_mul_of_nonneg_left (T.planted seam o inj X ix) (Finset.prod_nonneg fun i _ => hn i)
    _ = ∏ i, w i*T.rootTest β (X i) := Finset.prod_mul_distrib.symm
    _ ≤ ∏ i, M i := Finset.prod_le_prod (fun i _ => mul_nonneg (hn i) (T.root_nonneg ..)) (fun i _ => px i)

theorem purchased (R : Run G) (hG : G.Simple) {D : Campaign R} (walls : Campaign.Pillars R D)
    {ε : ℝ} (props : WilsonLimitConstruction.FundedOriginalProperties.{u} hG ε walls)
    (pace : WilsonWindowReportingPace.Slow R.kit) {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) {V : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
    {P : ∀ d, (ℕ×ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d} {b : Presentation R.family}
    (files : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (sale : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))
    {L B : ℝ} (hL : 0 < L) (hB : 4 ≤ B) {I : Type v} [Fintype I]
    (d : I → ℕ) (K : I → ℝ) (hK : ∀ i, 0 ≤ K i) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : I → ℝ, (∀ i, 0 ≤ M i) ∧ ∀ᶠ k in atTop, ∀ᶠ w : ℕ×ℕ in f.fuse,
      ∃ (hn : k ≤ w.1) (hp : port R.family L B hL k ≤ w.1),
        ∀ (J : Type v') [Fintype J] (row : J → I) (x : ∀ a, R.family.label (d (row a))),
        (∀ a, ‖x a‖ ≤ K (row a)) → ∀ (j : ℕ) (hm : j ≤ k) (_hj : j ≤ port R.family L B hL k)
        (o : J → Site (R.family.side w.1 w.2)) (v : J → Site (R.family.side j w.2)),
        let T := center R.family.S w.2 (hm.trans hn) (0 : Site (R.family.side w.1 w.2))
        Injective v → (∀ a, o a ∈ T.margin (v a) (3*Cells.span R.family.S hn w.2)) →
        (∀ a, o a ∈ T.margin (v a) (3*Cells.span R.family.S hp w.2)) →
        (∏ a, R.family.S.a k^(d (row a)))*‖moment (R.family.beta w.1 w.2) (fun U =>
          ∏ a, corrected R.family (V (d (row a))) w.1 w.2 (P (d (row a)) w) b (x a) (o a) U)‖ ≤
          ∏ a, M (row a)*Real.exp (δ*R.family.S.scale k) := by
  choose M hM sale' using fun i => WilsonMovingChildLease.purchased R hG walls props pace F files sale
    (d i) hL hB (K i) δ (hK i) hδ
  refine ⟨M,hM,?_⟩
  filter_upwards [eventually_all.mpr sale'] with k ready
  have late (n : ℕ) : ∀ᶠ w : ℕ×ℕ in f.fuse, n ≤ w.1 :=
    (Order.fused f _).mpr (Eventually.of_forall fun _ => f.mesh.cofinal.eventually (eventually_ge_atTop n))
  filter_upwards [eventually_all.mpr ready,late k,late (port R.family L B hL k)] with w state hk hp
  refine ⟨hk,hp,?_⟩; intro J inst row x hx j hm hj o v T inj near far
  apply placed T (seamless R.makes w.1 w.2) v inj _ _ _
  · intro a; exact pow_nonneg (R.family.S.a_pos k).le _
  · intro a; obtain ⟨_,_,q⟩ := state (row a)
    exact q (x a) (hx a) j hm hj (o a) (v a) (near a) (far a)

end YM.Integration.WilsonMovingChildProduct
