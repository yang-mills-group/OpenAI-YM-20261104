import YM.Integration.WilsonOffsetDiscrepancyLease

/-! Price the complete corrected child, with its actual cutoff location and
its two genuine signed terms, on a single late physical extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingChildLease
open Function Set Filter Lattice Cells Wilson RG RG16 RG16.Literal Labels Source Push Extraction
open Next.Extract MergeProof PhysicalNext.Repeat.Legato WilsonOffsetReportingProducts
open scoped Classical Topology
universe u
variable {G : Gauge}

theorem scaled (S : Schedule) (k d : ℕ) (δ : ℝ) :
    S.a k^d*(S.a k)^(-(d:ℝ)-δ) = Real.exp (δ*S.scale k) := by
  rw [← Real.rpow_natCast,← Real.rpow_add (S.a_pos k),show (d:ℝ)+(-(d:ℝ)-δ) = -δ by ring,
    Real.rpow_def_of_pos (S.a_pos k),Schedule.scale,Real.log_inv]; congr 1; ring

theorem combined {n : Side} (T : Tiling n) (v : T.Cell) (X Y : Config G n → ℂ) :
    T.copy v (X+Y) = T.copy v X + T.copy v Y := by
  funext U; by_cases h:T.hand v <;> simp [Tiling.copy,h]

theorem purchased (R : Run G) (hG : G.Simple) {D : Campaign R} (walls : Campaign.Pillars R D)
    {ε : ℝ} (props : WilsonLimitConstruction.FundedOriginalProperties.{u} hG ε walls)
    (pace : WilsonWindowReportingPace.Slow R.kit) {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) {V : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
    {P : ∀ d, (ℕ×ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d} {b : Presentation R.family}
    (files : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (sale : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) (d : ℕ)
    {L B : ℝ} (hL : 0 < L) (hB : 4 ≤ B) (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ k in atTop, ∀ᶠ w : ℕ×ℕ in f.fuse,
      ∃ (hn : k ≤ w.1) (hp : port R.family L B hL k ≤ w.1),
        ∀ (x : R.family.label d), ‖x‖ ≤ K → ∀ (j : ℕ) (hm : j ≤ k)
        (_hj : j ≤ port R.family L B hL k) (o : Site (R.family.side w.1 w.2))
        (v : Site (R.family.side j w.2)),
        let T := center R.family.S w.2 (hm.trans hn) (0 : Site (R.family.side w.1 w.2))
        o ∈ T.margin v (3*Cells.span R.family.S hn w.2) →
        o ∈ T.margin v (3*Cells.span R.family.S hp w.2) →
        ∃ X : Config G (R.family.side w.1 w.2) → ℂ, Interior (T.chamber 0) X ∧
          R.family.S.a k^d*T.rootTest (R.family.beta w.1 w.2) X ≤ M*Real.exp (δ*R.family.S.scale k) ∧
          T.copy v X = corrected R.family (V d) w.1 w.2 (P d w) b x o := by
  let C := R.family
  obtain ⟨k₀,H,hH,paid⟩ := WilsonOffsetPrimaryLease.purchased R F sale d K δ hK hδ
  obtain ⟨A,_,floor,subp,_,cash⟩ := WilsonOffsetDiscrepancyLease.purchased R hG walls props pace files sale d hL hB
  obtain ⟨Z,hZ,z⟩ := subp δ hδ
  have zpos : 0 ≤ Z := le_trans zero_le_one hZ
  refine ⟨H+1+K*Z,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop k₀,cash] with k hk finance
  let E := Real.exp (δ*C.S.scale k)
  let a := C.S.a k ^ d
  have ha : 0 < a := pow_pos (C.S.a_pos k) d
  have hE : 0 < E := Real.exp_pos _
  have cutoff (n : ℕ) : ∀ᶠ w : ℕ×ℕ in f.fuse, n ≤ w.1 :=
    (Order.fused f _).mpr (Eventually.of_forall fun _ => f.mesh.cofinal.eventually (eventually_ge_atTop n))
  filter_upwards [paid k hk (E/a) (div_pos hE ha),cutoff (k+1),cutoff (port C L B hL k)] with w prim late hp
  obtain ⟨hn,prim⟩ := prim
  refine ⟨hn,hp,?_⟩; intro x hx j hm hj o v T fit₁ fit₂
  obtain ⟨X,ix,px,cx⟩ := prim x hx j hm o v fit₁
  obtain ⟨Y,iy,py,cy⟩ := finance w.1 late w.2 hp x j hj o v fit₂
  refine ⟨X+Y,ix.plus iy,?_,?_⟩
  · have triangle := (seamless R.makes w.1 w.2).semi T X Y ix iy
    have engineering : a*(H*(C.S.a k)^(-(d:ℝ)-δ)+E/a) = H*E+E := by
      rw [mul_add,← mul_assoc, mul_comm a H, mul_assoc,show a*(C.S.a k)^(-(d:ℝ)-δ) = E from scaled ..,
        mul_div_cancel₀ _ ha.ne']
    calc
      a*T.rootTest _ (X+Y) ≤ a*(T.rootTest _ X+T.rootTest _ Y) := mul_le_mul_of_nonneg_left triangle ha.le
      _ = a*T.rootTest _ X+a*T.rootTest _ Y := mul_add ..
      _ ≤ a*(H*(C.S.a k)^(-(d:ℝ)-δ)+E/a)+‖x‖*A k := add_le_add (mul_le_mul_of_nonneg_left px ha.le) py
      _ = H*E+E+‖x‖*A k := by rw [engineering]
      _ ≤ H*E+E+K*(Z*E) := add_le_add_right (mul_le_mul hx (z k) (zero_le_one.trans (floor k)) hK) _
      _ = (H+1+K*Z)*E := by ring
  · exact (combined T v X Y).trans (congrArg₂ (·+·) cx cy)

end YM.Integration.WilsonMovingChildLease
