import YM.Integration.WilsonAddressedWeakPointCells

/-! Cover representatives of the actual projected detector sites. The lifts
are chosen from the same centered residues that occur in the Wilson block. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakAncestor
open Function Filter Set MeasureTheory Lattice RG Source Extraction Table Spec PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)

private theorem centered {m n : Side} (g : Ratio m n) (q : Cover) :
    ∃ b : Cover, g.parent (wrap n q) = wrap m b ∧
      q = g.count.val • b + lift (wrap g.count q) := by
  let c := lift (wrap g.count q)
  have eqv : wrap g.count c = wrap g.count q := wrap_lift _
  have divs (j : Axis) : (g.count.val:ℤ) ∣ q j - c j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congrFun eqv j)
  choose b hb using divs
  have sum : q = g.count.val • b + c := by
    funext j
    change q j = g.count.val • b j + c j
    rw [nsmul_eq_mul]
    linarith only [hb j]
  refine ⟨b,?_,sum⟩
  have same : g.assemble (wrap m b,wrap g.count q) = wrap n q := by
    rw [Ratio.assemble,g.embed_wrap,←map_add]
    exact congrArg (wrap n) sum.symm
  rw [←same,g.assemble_parent]

private theorem axes {x y : Points 2} {b : ℝ} (hb : 0 < b)
    (close : ∀ i j, |x i j - y i j| ≤ b) : dist x y ≤ 8*b := by
  let E := x-y
  rw [dist_eq_norm]
  change ‖E‖ ≤ 8*b
  rw [←sq_le_sq₀ (norm_nonneg _) (by positivity),←(Points.flatten.norm_map E),EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ ∑ _ : Fin 2 × Axis, b^2 := Finset.sum_le_sum fun i _=> sq_le_sq.mpr (by
         rw [abs_of_pos hb]; exact close i.1 i.2)
       _ ≤ _ := by
         simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
           Nat.cast_mul,Nat.cast_ofNat]
         norm_num
         nlinarith [sq_nonneg b]

theorem original (N p k : ℕ) (hk : k ≤ N) (ρ : ℝ) (hρ : 0 < ρ) (x : Points 2) :
    ∃ b : Fin 2 → Cover,
      (∀ i, (R.family.S.toDepth hk p).parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i) =
        wrap (R.family.side k p) (b i)) ∧
      dist (ρ⁻¹ • tag (R.family.S.a k) b) x ≤ 16 * (R.family.S.a k / ρ) := by
  let S := R.family.S
  let K := S.toDepth hk p
  let q := address (S.a N) (ρ • x)
  choose b par back using fun i : Fin 2 => centered K (q i)
  refine ⟨b,par,?_⟩
  have scale : S.a N * K.count.val = S.a k := S.embeds_scale K
  have h₁ (i : Fin 2) (a : Axis) :
      |tag (S.a k) b i a - tag (S.a N) q i a| ≤ S.a k := by
    let c := lift (wrap K.count (q i))
    have split : q i a = K.count.val • b i a + c a := congrFun (back i) a
    have cent : -(K.count.val : ℤ) < 2*c a ∧ 2*c a ≤ K.count.val := lift_centers (wrap K.count (q i)) a
    have bound : |(c a:ℝ)| ≤ K.count.val := by
      have zr : |c a| ≤ (K.count.val:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
      exact_mod_cast zr
    have sr : (q i a:ℝ) = K.count.val * (b i a:ℝ) + (c a:ℝ) := by
      rw [nsmul_eq_mul] at split
      exact_mod_cast split
    change |S.a k * (b i a:ℝ) - S.a N * (q i a:ℝ)| ≤ _
    rw [←scale,sr,show S.a N * K.count.val * (b i a:ℝ) - S.a N *
      (K.count.val * (b i a:ℝ) + (c a:ℝ)) = -(S.a N * (c a:ℝ)) by ring,
      abs_neg,abs_mul,abs_of_pos (S.a_pos _)]
    exact mul_le_mul_of_nonneg_left bound (S.a_pos _).le
  have near : dist (tag (S.a k) b) (ρ • x) ≤ 8*(2*S.a k) := by
    apply axes (mul_pos zero_lt_two (S.a_pos k))
    intro i a
    calc _ ≤ |tag (S.a k) b i a - tag (S.a N) q i a| +
               |tag (S.a N) q i a - (ρ • x) i a| := abs_sub_le .. 
         _ ≤ S.a k + S.a N := add_le_add (h₁ i a) (coord_grid_bound (S.a_pos N) (ρ • x) i a)
         _ ≤ _ := by linarith only [S.strictAnti.antitone hk]
  have undo : ρ⁻¹ • (tag (S.a k) b - ρ • x) = ρ⁻¹ • tag (S.a k) b - x := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hρ.ne',one_smul]
  rw [dist_eq_norm,←undo,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hρ).le]
  rw [dist_eq_norm] at near
  calc _ ≤ ρ⁻¹ * (8*(2*S.a k)) := mul_le_mul_of_nonneg_left near (inv_pos.mpr hρ).le
       _ = _ := by rw [div_eq_mul_inv]; ring

end YM.Integration.WilsonAddressedWeakAncestor
