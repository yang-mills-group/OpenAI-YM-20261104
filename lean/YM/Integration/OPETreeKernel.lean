import YM.Integration.OPETreeRemainder

/-! Jointly smooth extension of the normalized free cluster through zero
radius. Inner contractions retain their separated shape covariance. Each
mixed leg carries its own positive power of the cluster radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OPETreeKernel
open Function Set Filter Finsupp Next.Rank.Normal
open Maxwell Maxwell.Free Maxwell.Wick MSbar.OPE Pert.Position
open FVA2 RG11.Fields RG11.Grove RG11.Neighborhood OPETreeRemainder
open scoped Classical BigOperators ContDiff Topology

section Gaussian
variable {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {Q : A → Symmetric V} {atPoint : A}
    (hQ : ∀ i j, ContDiffAt ℝ ∞ (fun a => (Q a).cov i j) atPoint)
include hQ

private theorem glyph_smooth {I : Type*} (z : I → V) (s : Finset I) :
    ContDiffAt ℝ ∞ (fun x => blend (Q x) 0 (glyphs z s)) atPoint := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with hs | ⟨i,hi⟩
    · subst s; simp only [glyphs, Finset.prod_empty, fresh]; exact contDiffAt_const
    have hsub := Finset.erase_ssubset hi
    rw [← Finset.insert_erase hi]
    simp_rw [spring _ _ _ _ (Finset.notMem_erase i s)]
    exact (contDiffAt_const.mul (ih _ hsub)).add
      (ContDiffAt.sum fun a _ => (hQ (z i) (z a)).mul
        (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset a _) hsub)))

theorem gaussian_smooth (p : poly V) :
    ContDiffAt ℝ ∞ (fun x => blend (Q x) 0 p) atPoint := by
  let B := MvPolynomial.basisMonomials V ℂ
  have hb i : ContDiffAt ℝ ∞ (fun x => blend (Q x) 0 (B i)) atPoint := by
    obtain ⟨v,hv,_⟩ := Maxwell.Free.mon_list i
    rw [show B i = glyphs v.get Finset.univ from ?_]
    · exact glyph_smooth hQ _ _
    rw [glyphs, ← List.prod_ofFn]
    exact hv.trans (congrArg List.prod (calc
      _ = (List.ofFn v.get).map _ := by rw [List.ofFn_get]
      _ = _ := List.map_ofFn))
  let c := B.repr p
  rw [show p = ∑ i ∈ c.support, c i • B i from (B.linearCombination_repr p).symm]
  simp_rw [_root_.map_sum, map_smul, smul_eq_mul]
  exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (hb i)
end Gaussian

variable {G : Gauge} {n m i d : ℕ}

def shapeFrame (x : Points n) : Symmetric (Mark G n) :=
  if hx : x ∈ conf n then frameX hx else 0

theorem coordinate_smooth (i : Fin n) :
    ContDiff ℝ ∞ (fun a : ℝ × Points n => a.2 i) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)
  exact ((contDiff_apply ℝ _ i).comp L.contDiff).comp contDiff_snd

theorem shape_smooth (a : ℝ × Points n) (hx : a.2 ∈ conf n) (u v : Mark G n) :
    ContDiffAt ℝ ∞ (fun b : ℝ × Points n => (shapeFrame b.2).cov u v) a := by
  have hN : ∀ᶠ b : ℝ × Points n in 𝓝 a, b.2 ∈ conf n :=
    continuous_snd.continuousAt.eventually ((conf_open n).mem_nhds hx)
  by_cases h : u.1 = v.1
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hN] with b hb
    simp only [shapeFrame, dif_pos hb, frameX, if_pos h]
  have hE := (entry_smooth u.2 v.2
    (x := (a.2 u.1,a.2 v.1)) ((show Injective a.2.ofLp from hx).ne h)).comp a
      ((coordinate_smooth u.1).contDiffAt.prodMk (coordinate_smooth v.1).contDiffAt)
  apply hE.congr_of_eventuallyEq
  filter_upwards [hN] with b hb
  simp only [shapeFrame, dif_pos hb, frameX, if_neg h, Function.comp_apply]

def kernel (y : Tail m) (p : Fin n → WickPol G) (q : Fin m → WickPol G)
    (a : ℝ × Points n) : ℂ :=
  mixed (shapeFrame a.2) (frameX (Points.tail_in y.apart))
    (changed (edges (inside a.2 a.1 y.c) y.y) (readW markW (a.1 : ℂ)))
    (pot Finset.univ p) (pot Finset.univ q)

theorem smooth_at (y : Tail m) (p : Fin n → WickPol G) (q : Fin m → WickPol G)
    (a : ℝ × Points n) (hx : a.2 ∈ conf n) (hfar : foreign (inside a.2 a.1 y.c) y.y) :
    ContDiffAt ℝ ∞ (kernel y p q) a := by
  have hmix (u : Mark G n) (v : Mark G m) :
      ContDiffAt ℝ ∞ (fun b : ℝ × Points n =>
        changed (edges (inside b.2 b.1 y.c) y.y) (readW markW (b.1:ℂ)) u v) a := by
    simp only [changed, readW, linearCombination_single, Pi.smul_apply, smul_eq_mul]
    have hentry := (entry_smooth u.2 v.2 (x := (inside a.2 a.1 y.c u.1, y.y v.1))
      (hfar u.1 v.1)).comp a (f := fun b : ℝ × Points n => (y.c+b.1 • b.2 u.1,y.y v.1))
        ((contDiffAt_const.add (contDiffAt_fst.smul
          (coordinate_smooth u.1).contDiffAt)).prodMk contDiffAt_const)
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp a contDiffAt_fst).pow _).mul hentry
  apply gaussian_smooth
  intro u v
  cases u <;> cases v
  · exact shape_smooth a hx _ _
  · exact hmix _ _
  · exact hmix _ _
  exact contDiffAt_const

theorem at_zero (y : Tail m) (p : Fin n → WickPol G) (q : Fin m → WickPol G)
    (x : Points n) (hx : x ∈ conf n) : ContDiffAt ℝ ∞ (kernel y p q) (0,x) := by
  apply smooth_at y p q _ hx
  intro i j
  change y.c+(0:ℝ) • x i ≠ y.y j
  rw [zero_smul,add_zero]
  exact exterior_apart y (0 : Fin 1) j

variable (V : Warehouse G) {Q : MS.Land.Booked (FVA2.ColorCode.wings G)}
    (M : MS.Land.MS_Data G Q) (μ : ℝ)

/-- The original independent MS degree-zero correlation agrees with
the indicated smooth function at every positive collision-free radius. -/
theorem normalized (x : conf n) (y : Tail m) (v : Fin n → E V.F i) (w : Fin m → E V.F d)
    (weights : Fin n → ℕ) (hv : ∀ a, pureW scaleW (weights a) (polynomials V.F i v a))
    (r : ℝ) (hr : 0 < r) (hfar : foreign (inside x.val r y.c) y.y) :
    (r : ℂ)^(∑ a,weights a) * paired V M μ 0 (driven r x.val y) v w =
      kernel y (polynomials V.F i v) (polynomials V.F d w) (r,x.val) := by
  have hj : driven r x.val y ∈ conf (n+m) :=
    combination (safe x.property y.c hr) (Points.tail_in y.apart) hfar
  rw [paired_tree V M μ (driven r x.val y) hj]
  change (r:ℂ)^_ * MSbar.Tree.finitePart 1 (combo (inside x.val r y.c) y.y) _ = _
  rw [kernel, shapeFrame, dif_pos x.property]
  exact (priced x.property hv hr y.c (Points.tail_in y.apart) hfar _).trans
    (splitCluster ..).symm

end YM.Integration.OPETreeKernel
