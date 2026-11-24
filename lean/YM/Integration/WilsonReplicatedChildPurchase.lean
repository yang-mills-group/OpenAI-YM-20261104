import YM.Integration.WilsonMovingChildProduct
import YM.Integration.WilsonMovingChildReflection
import YM.Integration.WilsonReplicatedOffsetProducts

/-! The original signed product on the physical outer replication board.
All fine children keep their literal offsets, orientations and complex phases. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReplicatedChildPurchase
open Function Set Filter Lattice Cells Wilson RG RG16 RG16.Literal Labels Source Push Extraction
open Next.Extract MergeProof PhysicalNext.Repeat.Legato WilsonOffsetReportingProducts WilsonMovingChildReflection
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {n : Side}

def Fits (S : Schedule) {N p h k t : ℕ} (hk : k ≤ N) (ht : t ≤ N) (hh : h ≤ N)
    {I : Type} (A : Tiling (S.side N p)) (o : I → Site (S.side N p)) (v : A.Cell×I → Site (S.side h p)) :=
  Injective (fun a : A.Cell×I => (A.omega a.1).act (v a)) ∧
    ∀ a : A.Cell×I, before A a.1 (o a.2) ∈ (center S p hh 0).margin (v a) (3*Cells.span S hk p) ∧
      before A a.1 (o a.2) ∈ (center S p hh 0).margin (v a) (3*Cells.span S ht p)

theorem account {I : Type} [Fintype I] (A T : Tiling n) (β : ℝ) (seam : Seam G n β)
    (F : I → Config G n → ℂ) (v : A.Cell×I → T.Cell) (hv : Injective v) (g M : I → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hM : ∀ i, 0 ≤ M i)
    (issued : ∀ a : A.Cell×I, ∃ X, Interior (T.chamber 0) X ∧
      g a.2*T.rootTest β X ≤ M a.2 ∧ T.copy (v a) X = A.copy a.1 (F a.2)) :
    (∏ i, g i)*A.rootTest β (fun U => ∏ i, F i U) ≤ ∏ i, M i := by
  have leased := WilsonMovingChildProduct.placed T seam v hv (fun a : A.Cell×I => A.copy a.1 (F a.2))
    (fun a => g a.2) (fun a => M a.2) (fun a => hg a.2) issued
  have eq : (fun U => ∏ a : A.Cell×I, A.copy a.1 (F a.2) U) = A.fullAt (fun _ U => ∏ i, F i U) := by
    funext U; rw [Fintype.prod_prod_type]; apply Finset.prod_congr rfl; intro i _
    unfold Tiling.copy; split_ifs <;> simp only [star_prod]
  rw [eq,Fintype.prod_prod_type,Fintype.prod_prod_type] at leased
  simp only [Finset.prod_const,Finset.card_univ] at leased
  apply (pow_le_pow_iff_left₀ (mul_nonneg (Finset.prod_nonneg fun i _ => hg i) (A.root_nonneg ..))
    (Finset.prod_nonneg fun i _ => hM i) A.cells_positive.ne').mp
  rw [mul_pow,A.powering]; exact leased

theorem purchased (R : Run G) (hG : G.Simple) {D : Campaign R} (walls : Campaign.Pillars R D)
    {ε : ℝ} (props : WilsonLimitConstruction.FundedOriginalProperties.{u} hG ε walls)
    (pace : WilsonWindowReportingPace.Slow R.kit) {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) {V : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
    {P : ∀ d, (ℕ×ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d} {b : Presentation R.family}
    (files : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (sale : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))
    {L B : ℝ} (hL : 0 < L) (hB : 4 ≤ B) :
    ∃ radius : ℕ → ℕ, ∀ {I : Type} [Fintype I] (d : I → ℕ) (K : I → ℝ), (∀ i, 0 ≤ K i) →
      ∀ δ : ℝ, 0 < δ → ∃ M : I → ℝ, (∀ i, 0 ≤ M i) ∧ ∀ᶠ k in atTop, ∀ᶠ w : ℕ×ℕ in f.fuse,
        ∃ (hn : k ≤ w.1) (hp : port R.family L B hL k ≤ w.1),
          ∀ (x : ∀ i, R.family.label (d i)), (∀ i, ‖x i‖ ≤ K i) → ∀ (j : ℕ) (hm : j ≤ k)
          (_hj : j ≤ port R.family L B hL k) (A : Tiling (R.family.side w.1 w.2))
          (o : I → Site (R.family.side w.1 w.2)) (v : A.Cell×I → Site (R.family.side j w.2)),
          Fits R.family.S hn hp (hm.trans hn) A o v → WilsonReplicatedOffsetProducts.AvoidsCopies V radius d A o →
          (∏ i, R.family.S.a k^(d i))*A.rootTest (R.family.beta w.1 w.2)
            (fun U => ∏ i, R.family.O w.1 w.2 (x i) (o i) U) ≤ ∏ i, M i*Real.exp (δ*R.family.S.scale k) := by
  obtain ⟨radius,restore⟩ := WilsonReplicatedOffsetProducts.on_issued R V W P b files sale
  refine ⟨radius,?_⟩; intro I _ d K hK δ hδ
  choose M hM cash using fun i => WilsonMovingChildLease.purchased R hG walls props pace F files sale
    (d i) hL hB (K i) δ (hK i) hδ
  refine ⟨M,hM,?_⟩
  obtain ⟨n₀,restore⟩:=eventually_atTop.mp (restore I d)
  filter_upwards [eventually_all.mpr cash] with k paid
  have late (n : ℕ) : ∀ᶠ w : ℕ×ℕ in f.fuse, n ≤ w.1 :=
    (Order.fused f _).mpr (Eventually.of_forall fun _ => f.mesh.cofinal.eventually (eventually_ge_atTop n))
  filter_upwards [eventually_all.mpr paid,late k,late (port R.family L B hL k),late n₀] with w now hn hp ready
  refine ⟨hn,hp,?_⟩; intro x hx j hm hj A o v fit far
  rw [restore w.1 ready w.2 x o A far]
  let T := center R.family.S w.2 (hm.trans hn) (0 : Site (R.family.side w.1 w.2))
  apply account A T _ (seamless R.makes w.1 w.2) _ (fun a : A.Cell×I => (A.omega a.1).act (v a)) fit.1
    _ _ (fun i => pow_nonneg (R.family.S.a_pos k).le (d i)) (fun i => mul_nonneg (hM i) (Real.exp_pos _).le)
  intro a
  obtain ⟨_,_,funded⟩ := now a.2
  let Z := corrected R.family (V (d a.2)) w.1 w.2 (P (d a.2) w) b (x a.2)
  exact reflected R.family.S (hm.trans hn) (R.family.beta w.1 w.2) _ _ A a.1 (o a.2) (v a) Z
    (fun z => WilsonMovingChildReflection.place ..) (funded (x a.2) (hx a.2) j hm hj
      (before A a.1 (o a.2)) (v a) (fit.2 a).1 (fit.2 a).2)

end YM.Integration.WilsonReplicatedChildPurchase
