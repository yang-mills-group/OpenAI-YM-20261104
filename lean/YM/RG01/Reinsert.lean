import YM.RG01.Listing

/-! # Reinsert the cut into the full unnormalised density
Pointwise, including flagged U. Sign is that of a negative log; paths, scalar,
alpha receipt and K remain exactly in `front`. Never reads p.mask derivatives.
This is a split within the same logarithm representation; full densities are not
additive in that input and no approximation to them by dropping the remainder in
the exponent is made. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.List
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Greenbelt Match Song
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R R' : RG.Rep G f} {μ q C' d v Y A b r B s α a i C Λ δ e β τ ξ γ : ℝ} {k j : ℕ}
    {χ : Chi} {H : Cash W s μ L Q o α T R} {J : Cash W s μ L Q o α T R'} {p : BudgetPoint}
    (X : Alliance H J 1 0)

/-- General compatibility with the same-Listing decomposition. -/
lemma series {G : Gauge} {c:Side} {p : BudgetPoint} {L : Listing G c} {V : Collection.Source G c}
    (h : (L.read V).EBound p a) (U : Config G c) :
    Summable fun i=> (L.read V).regularOccurrence p i U := by
  obtain ⟨k,hk,hE⟩:=Activities.E_total h
  refine hk.of_norm_bounded fun i=>?_ ; unfold Activities.regularOccurrence
  by_cases he:Healthy p.threshold (L.read V|>.reg i).support U
  · rw [RG.masked_eq _ _ _ _ he]
    exact (hE i).2 U he [] (Nat.zero_le _) (by simp)
  rw [RG.masked_ne _ _ _ _ he,norm_zero]; exact (hE i).1

lemma same_listing {L : Listing G c} {x y z : Collection.Source G c}
    (hr : y.logRead + z.logRead=x.logRead) (hh : z.hardRead=x.hardRead)
    (hx : (L.read x).EBound p a) (hy : (L.read y).EBound p b)
    (P : PathData G) (C : Clip) (U : Config G c) (β τ γ : ℝ) :
    Summable (fun i=> (L.read z).regularOccurrence p i U) ∧
      earlyValue L P C p x β τ γ U=Real.exp (- ((L.read y).additive p U)) * earlyValue L P C p z β τ γ U := by
  let F (v:Collection.Source G c) (i:ℕ):=(L.read v).regularOccurrence p i U
  have hf : F y + F z = F x:= by
    funext i; change masked _ (L.reg i).support (y.logRead i) _ + masked _ (L.reg i).support (z.logRead i) _=masked _ (L.reg i).support (x.logRead i) _
    by_cases h:Healthy p.threshold (L.reg i).support U
    · simp_rw [masked_eq _ _ _ _ h]; exact congr_fun (congr_fun hr i) U
    simp_rw [masked_ne _ _ _ _ h,add_zero]
  have hs : Summable (F y) := series hy U
  have ht : Summable (F z) := by
    rw [show F z=F x - F y from eq_sub_of_add_eq ((add_comm ..).trans hf)]
    exact (series hx U).sub hs
  have hk : (L.read x).additive p U= (L.read y).additive p U + (L.read z).additive p U := by
    change ∑' i, F x i=_
    exact hf ▸ hs.tsum_add ht -- direction
  have he : (L.read x).gas p U=(L.read z).gas p U:=by
    unfold Activities.gas Activities.gasOccurrence Activities.admissible
    dsimp only [Listing.read]; rw [hh]; exact rfl
  refine ⟨ht,?_⟩
  unfold earlyValue RG.Rep.eval RG.Rep.exponent; dsimp only [Collection.frozen]
  rw [hk,he,show τ*↑(Fintype.card (Site c)) - PathData.inChannels P C p β U - ((L.read y).additive p U + (L.read z).additive p U) = -(L.read y).additive p U + (τ*↑(Fintype.card (Site c)) - PathData.inChannels P C p β U - (L.read z).additive p U) from by ring,Real.exp_add]; ring

/-- The exact estimated piece is literally what, reinserted, gives the full
density on *all* fields. Includes original mask. No assertion about clipping or
new predicates introduced by later work. -/
lemma reinsert (est : Collection.Local (posting p H) p (plusone H X χ γ) δ e)
    (test : J.fragrances → Prop) (ht : Budget p (posting p H).reg ((tail (χ:=χ) X test).logRead) a)
    (P : PathData G) (C : Clip) (U : Config G c) (β τ : ℝ) :
    let L:=posting p H; let F:=plusone H X χ γ; let y:=tail (χ:=χ) X test; let z:=front (χ:=χ) X test γ
    Summable (fun i=> (L.read z).regularOccurrence p i U) ∧
      earlyValue L P C p F β τ γ U=
        Real.exp (- ((L.read y).additive p U)) * earlyValue L P C p z β τ γ U := by
  intro L F y z
  apply same_listing (funext (at_split X test γ)) rfl est.unweighted ht.unweighted

/-- The forced side of the atlas also carries the stronger full reserve. -/
lemma hard_budget {X : Listing G c} {F : Collection.Source G c}
    (h : Collection.Local X p F a b) : (X.read F).KBound p b := by
  obtain ⟨u,he,hK⟩:= h.expensive
  refine ⟨u,he,fun x=> budget_mono (hK x) ?_ ?_⟩
  · intro i
    split
    next _ => apply mul_nonneg (Real.exp_pos _).le (he i).1
    exact le_rfl
  · intro i
    dsimp only
    change (if x ∈ (X.hard i).support then p.mass (X.hard i).support (u i) else 0) ≤ _
    split
    next h =>
      rw [RG.BudgetPoint.mass]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (he i).1
      apply Real.exp_monotone
      gcongr
      exact le_add_of_nonneg_right zero_le_one
    exact le_rfl

end YM.RG01.List
