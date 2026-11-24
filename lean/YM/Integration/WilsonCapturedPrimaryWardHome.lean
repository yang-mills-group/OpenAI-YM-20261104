import YM.Integration.WilsonCapturedPrimaryWardFile
import YM.FullVolume.Ocean
import YM.Work.D01
import YM.Contact.NestedRaw

/-! Original Wilson and Haar-equation root tests at their common home. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardHome
open Function Filter Set MeasureTheory Lattice RG Labels Wilson Source Bid Cells Push
open PhysicalNext.Repeat.Legato WilsonLimitConstruction MergeProof FullVolume Extraction Next.Extract
open Extra.Histories Ribbons Extraction.Lease Org RelayDifference
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)
local notation "C" => R.family

theorem measured {f : Extraction.Order} (room : CellHyp R.family f) (d : ℕ) :
    ∃ k₀ : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ k ≥ k₀,
    ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ x : R.family.label d,
      BlockCost (Q:=(C).S) ((C).O z.1 z.2 x 0) k ((C).beta z.1 z.2)
        ((A*(C).S.a k^(-(d:ℝ)-1)+1)*(1+‖x‖)) := by
  obtain ⟨k₀,_,A,positive,priced⟩ := room.centered d 1 1 zero_lt_one zero_lt_one
  refine ⟨k₀,A,positive,fun k age=>?_⟩
  rw [Extraction.Order.fused]
  apply (priced k age 1 zero_lt_one).mono
  intro N period
  apply period.mono
  rintro p ⟨hk,bank⟩ x
  let B := 1+‖x‖
  have bpos : 0 < B := by dsimp [B]; positivity
  have nz : (B:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr bpos.ne'
  let v : (C).label d := (B:ℂ)⁻¹ • x
  have fits : ‖v‖ ≤ 1 := by
    rw [show ‖v‖=‖x‖/B by simp [v,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos bpos,div_eq_inv_mul]]
    exact (div_le_one bpos).mpr (by dsimp [B]; linarith)
  have back : (B:ℂ) • v=x := by simp [v,smul_smul,nz]
  have physical : (C).O (f.mesh p) (f.per N) x 0 = (B:ℂ) • (C).O (f.mesh p) (f.per N) v 0 := by
    have h := (((C).linearO (f.mesh p) (f.per N) d 0).mk' _).map_smul (B:ℂ) v
    change (C).O (f.mesh p) (f.per N) ((B:ℂ) • v) 0 = (B:ℂ) • (C).O (f.mesh p) (f.per N) v 0 at h
    rwa [back] at h
  obtain ⟨safe,price⟩ := bank v fits 0
  refine ⟨hk,?_,?_⟩
  · rw [physical]
    exact safe.scale _
  · rw [physical,Next.Extract.root_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos bpos,mul_comm _ (1+‖x‖)]
    exact mul_le_mul_of_nonneg_left price bpos.le

private def read {d : ℕ} (V : SectionData (R.family.labels.level d)) (N p : ℕ)
    (o : Site (R.family.side N p)) : R.family.label d →ₗ[ℂ] (Config G (R.family.side N p) → ℂ) where
  toFun v := initial V R.family.path N p v o
  map_add' x y := by
    funext u
    simp [initial,SectionData.places,V.eval_linear.map_add,mul_add]
  map_smul' q v := by
    funext u
    simp only [initial,map_smul,SectionData.places,V.eval_linear.map_smul,Pi.smul_apply]
    exact smul_comm _ _ _

/-- The difference of the actual calibrated Wilson cylinder and the exact
alternate equation stencil on the same family. -/
private def row {d : ℕ} (V : SectionData (R.family.labels.level d))
    (U : ℕ → ℕ → R.family.label d ≃ₗ[ℂ] R.family.label d) (N p : ℕ)
    (o : Site (R.family.side N p)) : R.family.label d →ₗ[ℂ] (Config G (R.family.side N p) → ℂ) :=
  (((R.family.linearO N p d o).mk' _).comp
    (((R.family.factory d N p).terminal).toLinearMap.comp (U N p).toLinearMap)) - read R V N p o

section coordinates
variable {d : ℕ}
local notation "F" => R.family.labels.level d
variable {V : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
  {P : ∀ d, (ℕ × ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)}
  {b : Presentation R.family} {ζ : ℕ → ℕ → ℝ}

private def bare (P : ∀ d, (ℕ × ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d))
    (b : Presentation R.family) (N p : ℕ) (x : R.family.label d) :=
  (P d (N,p)).symm ((R.family.factory d N p).terminal.symm (x-b.step d (N,p) x))

private theorem coefficients (house : Hearthside R.family V W P b ζ) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, ∀ x : R.family.label d,
      (F).coeffSize (bare R P b N p x) ≤
        2 * Fintype.card (F).Index * ‖x‖ * Real.exp (ε * R.family.S.scale N) := by
  obtain ⟨B,control⟩ := house.uniform d
  obtain ⟨E,Y,stamp⟩ := house.hearth d
  filter_upwards [Work.D01.terminal_ball (C) R.makes d (1+|B|) ε pos, stamp.stamped]
    with N price funded
  intro p x
  let c : ℂ := ‖x‖
  let y := c⁻¹ • x
  have scalar : ‖c‖ = ‖x‖ := Complex.norm_real _ |>.trans (Real.norm_of_nonneg (norm_nonneg _))
  by_cases zero : x=0
  · simp [zero,bare,Frame.coeffSize]
  have nz : c ≠ 0 := by simpa [c] using (norm_ne_zero_iff.mpr zero)
  have unit : ‖y‖ = 1 := by rw [show ‖y‖=‖c⁻¹‖*‖x‖ from norm_smul _ _, norm_inv, scalar, inv_mul_cancel₀ (norm_ne_zero_iff.mpr zero)]
  have norm_proj := ((b.step d (N,p)).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right ((control (N,p)).trans (le_abs_self B)) (norm_nonneg y))
  have inside : ‖y-b.step d (N,p) y‖ ≤ 1+|B| := by
    refine (norm_sub_le _ _).trans ?_
    simpa [unit] using add_le_add_left norm_proj ‖y‖
  let z := (R.family.factory d N p).terminal.symm (y-b.step d (N,p) y)
  have bound : ‖z‖ ≤ Real.exp (ε*R.family.S.scale N) := price p _ inside
  have mass : (F).coeffSize z ≤ Fintype.card (F).Index * Real.exp (ε*R.family.S.scale N) := by
    calc
      _ ≤ ∑ _i:(F).Index,Real.exp (ε*R.family.S.scale N) :=
        Finset.sum_le_sum fun i _ => (norm_le_pi_norm z i).trans bound
      _ = _ := by simp
  have raw := ((funded p).2.1 z).trans (mul_le_mul_of_nonneg_left mass (by norm_num))
  have back : c • y = x := by simp [y,smul_smul,nz]
  have scale : bare R P b N p x = c • bare R P b N p y := by
    calc
      _ = bare R P b N p (c • y) := congrArg _ back.symm
      _ = _ := by simp [bare,←smul_sub]
  rw [scale]
  change ∑ i:(F).Index,‖c • (bare R P b N p y) i‖ ≤ _
  simp_rw [norm_smul,scalar]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left raw (norm_nonneg x)).trans_eq (by ring)

private theorem projected {N p : ℕ} (x : R.family.label d) (o : Site (R.family.side N p)) :
    row R (V d) (fun n q=> P d (n,q)) N p o
      (bare R P b N p x) =
      WilsonOffsetReportingProducts.residual R.family (V d) N p (P d (N,p))
        (x-b.step d (N,p) x) o := by
  change R.family.O N p ((R.family.factory d N p).terminal ((P d (N,p)) (bare R P b N p x))) o -
    initial (V d) R.family.path N p (bare R P b N p x) o = _
  simp [bare,WilsonOffsetReportingProducts.residual,WilsonOffsetEquationLaw.incoming]

end coordinates

/-- One centered Wilson equation row, with its actual bare coordinates. -/
theorem difference {V : ∀ d, SectionData ((C).labels.level d)} {W : Mark.Weave G} {P b}
    (simple : G.Simple) (portfolio : ∀ d, Mark.Portfolio (C).params (V d) (W d))
    (house : Hearthside C V W P b (Bandage.fly R.alloy.B.a)) (d : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∀ p (v : (C).label d),
      BlockCost (Q:=(C).S)
        (row R (V d) (fun n q=>P d (n,q)) N p 0 v)
        k ((C).beta N p) (((C).labels.level d).coeffSize v * Real.exp (-(1/32:ℝ)*(C).S.scale N)) := by
  obtain ⟨E,Y,hY⟩ := house.hearth d
  let I := ((C).labels.level d).Index
  let basis (i:I) : (C).label d := Pi.single i 1
  have rows (i:I) := (ocean R.makes (R.again simple).1.tabs (V d) (portfolio d).valid hY
    (fun _=>basis i) (Sluggish.const (basis i))).2
  filter_upwards [eventually_all.mpr rows] with k data
  filter_upwards [eventually_all.mpr (fun i=>FullVolume.late.mp (data i)),eventually_ge_atTop k] with N stock h
  intro p v
  let L := row R (V d) (fun n q=>P d (n,q)) N p 0
  let S := center (C).S p h 0
  have tags (i:I) : Interior (S.chamber 0) (L (basis i)) ∧
      S.rootTest ((C).beta N p) (L (basis i)) ≤ Real.exp (-(1/32:ℝ)*(C).S.scale N) :=
    (stock i p).choose_spec
  have decompose : ∑ i:I,v i • basis i = v := by
    funext j
    rw [Finset.sum_apply,Finset.sum_eq_single j]
    · simp [basis]
    · intro i _ ij
      simp [basis,Ne.symm ij]
    · simp
  have priced := Next.UVStress.root_sum S ((C).beta N p) Finset.univ (fun i=>L (basis i))
    v (fun i _=>(tags i).1) (seamless R.makes N p)
  have complete : ∑ i,v i • L (basis i) = L v := by
    rw [←decompose,map_sum]
    simp only [map_smul]
    rw [decompose]
  rw [complete] at priced
  refine ⟨h,priced.1,priced.2.trans ?_⟩
  rw [Frame.coeffSize,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (tags i).2 (norm_nonneg _))

/-- Both terms arise from the same measured incoming coordinate, before the spatial
cell positions are read. The small factor belongs to the entire signed residual. -/
theorem original {V : ∀ d, SectionData ((C).labels.level d)} {W : Mark.Weave G} {P b}
    (simple : G.Simple) (portfolio : ∀ d, Mark.Portfolio (C).params (V d) (W d))
    (house : Hearthside C V W P b (Bandage.fly R.alloy.B.a)) (d : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∀ p (x : (C).label d),
      BlockCost (Q:=(C).S)
        (WilsonOffsetReportingProducts.residual C (V d) N p (P d (N,p)) (x-b.step d (N,p) x) 0)
        k ((C).beta N p) (2*Fintype.card ((C).labels.level d).Index*‖x‖*Real.exp (-(1/64:ℝ)*(C).S.scale N)) := by
  filter_upwards [difference R simple portfolio house d] with k rows
  filter_upwards [rows,coefficients R (d:=d) house (1/64) (by norm_num)] with N issued bounded
  intro p x
  have h := issued p (bare R P b N p x)
  rw [projected R x 0] at h
  refine ⟨h.stop,h.safe,h.amount.trans ?_⟩
  refine (mul_le_mul_of_nonneg_right (bounded p x) (Real.exp_pos _).le).trans_eq ?_
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

end YM.Integration.WilsonCapturedPrimaryWardHome
