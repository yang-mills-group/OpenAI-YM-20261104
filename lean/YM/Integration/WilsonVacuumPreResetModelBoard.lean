import YM.Integration.WilsonVacuumPreResetModelRegister
import YM.Integration.WilsonVacuumPreResetCurvaturePortfolio
import YM.Integration.WilsonVacuumPreResetLiftedPortfolio
import YM.Integration.WilsonVacuumPreResetPeriodField

/-! The three original signed kinetic families and the entire corrected
covering list on one pre-reset chart, including their rooted compact value. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetModelBoard
open Function Filter Lattice RG Wilson Marker WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat RG01Estimate IterationFour.Vacuum Extra.Iteration
open AnalyticBridge VerifiedReset Collection Quotes LocalComparison.Global
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Song Meadow Next.Scheduling WilsonStartup Geo
open WilsonVacuumPreResetPeriodEntries WilsonVacuumPreResetModelRegister WilsonVacuumPreResetCurvatureField
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

def source (A:Listing G n)(B:BudgetPoint)(K:PathData G)(c:Clip)(width paths γ β σ C:ℝ)
    (Z:SeriesA G)(k:ℕ→ℕ→ℝ)(t q:ℕ):Precise.Leads G n:=
  joined (WilsonVacuumPreResetCurvatureRack.model A B K c width paths γ β t q)
    (WilsonVacuumPreResetLiftedRack.model n B σ C k Z t q)

theorem original (simple:G.Simple)(hn:20<n.val)(A:Listing G n)(B:BudgetPoint)(K:PathData G)(c:Clip)
    {width paths Λ σ C:ℝ}(hc:K.Bounds c width paths Λ)(clip:Decent c B)
    (hw:preExponent B/B.B≤width/4)(hs:0<σ)(hz:preExponent B/B.B≤σ/4)(blocks:2≤B.B)
    (γ β:ℝ)(Z:SeriesA G)(draw:Draw Z σ C)(k:ℕ→ℕ→ℝ)(q:ℕ)(room:4≤q){η:ℝ}(ep:0<η):
    ∀ᶠt:ℕ in atTop,
      let J:=WilsonVacuumPreResetCurvatureRack.model A B K c width paths γ β t q
      let L:=WilsonVacuumPreResetLiftedRack.model n B σ C k Z t q
      let M:=source A B K c width paths γ β σ C Z k t q
      M.listing.hard=A.hard ∧ M.bill=J.bill+L.bill ∧
      Precise.Suggests B M ((WilsonVacuumPreResetLiftedPiece.rebate width (q+1)*J.bill+η)+
        (WilsonVacuumPreResetLiftedPiece.rebate σ (q+1)*L.bill+η)) M.bill ∧
      ∃P:Abacus.Rack M.listing (B.B+q) M.pioneers,
        P.polygon=(WilsonVacuumPreResetCurvatureRack.original A B K c width paths γ β t q).polygon+
          (WilsonVacuumPreResetLiftedRack.original (n:=n) B σ C k Z t q room).polygon:=by
  filter_upwards [WilsonVacuumPreResetCurvaturePortfolio.original A B K c hc clip hw γ β q ep,
    WilsonVacuumPreResetLiftedPortfolio.original simple hn B hs hz blocks Z draw k q ep] with t curv cover
  intro J L M
  refine ⟨rfl,rfl,purchased B J L curv cover,assembled J L le_rfl (Nat.le_add_left _ _)
    (WilsonVacuumPreResetCurvatureRack.original A B K c width paths γ β t q)
    (WilsonVacuumPreResetLiftedRack.original (n:=n) B σ C k Z t q room)⟩

private theorem summed (A:Listing G n)(B:BudgetPoint)(f:ℕ→ Config G n→ℝ){w:ℝ}(h:Meadow.Budget B A.reg f w)
    (U:Config G n):Summable fun i=>masked B.threshold (A.reg i).support (f i) U:=by
  let F:Collection.Source G n:=⟨f,0⟩
  obtain ⟨rate,early,stock⟩:=h
  have hp:(A.read F).EBound B w:=⟨rate,fun i=>(stock i).2,Quotes.segment A.reg (fun i=>(stock i).2.1) early⟩
  obtain ⟨b,hb,paid⟩:=Activities.E_total hp
  apply Summable.of_norm_bounded hb
  intro i
  by_cases quiet:Healthy B.threshold (A.reg i).support U
  · rw [masked_eq _ _ _ _ quiet]
    exact (paid i).2 U quiet [] (Nat.zero_le _) (by simp)
  · rw [masked_ne _ _ _ _ quiet,norm_zero]
    exact (paid i).1

theorem measured (simple:G.Simple)(hn:20<n.val)(A:Listing G n)(B:BudgetPoint)(K:PathData G)(c:Clip)
    {width paths Λ σ C:ℝ}(hc:K.Bounds c width paths Λ)
    (hs:0<σ)(hz:preExponent B/B.B≤σ/4)(blocks:2≤B.B)
    (γ β:ℝ)(Z:SeriesA G)(draw:Draw Z σ C)(k:ℕ→ℕ→ℝ)(t q:ℕ)(U:Config G n):
    let M:=source A B K c width paths γ β σ C Z k t q
    HasSum (fun i=>masked B.threshold (M.listing.reg i).support (M.trunk i) U)
      (γ*Collection.receipt K c B U+β*(billOf B K.cubic U+billOf B K.quartic U)+
        (entries n B σ C Z k).additive B U):=by
  intro M
  let T:=entries n B σ C Z k
  let v (i:Rows n):=masked B.threshold (strings K B (slot i)).support
    (WilsonVacuumPreResetCurvatureField.source K c γ β i) U
  let e:ℕ≃Rows n:=WilsonVacuumPreResetCurvatureRegister.number n
  let f:=v ∘ e
  let g (i:ℕ):=masked B.threshold (T.reg i).support (T.E i) U
  let a:=γ*Collection.receipt K c B U+β*(billOf B K.cubic U+billOf B K.quartic U)
  have terms:HasSum v a:=WilsonVacuumPreResetCurvatureField.original B K c hc γ β U
  have hf:HasSum f a:=(e.hasSum_iff (f:=v)).mpr terms
  have hg:HasSum g (T.additive B U):=(summed ⟨T.reg,T.forced⟩ B T.E
    (WilsonVacuumPreResetPeriodEntries.original simple hn B hs hz blocks Z draw k).1 U).hasSum
  let F:ℕ⊕ℕ→ℝ:=Sum.elim f g
  have hgather:HasSum F _:=HasSum.sum (f:=F) hf hg
  convert (Caddy.e.hasSum_iff (f:=F)).mpr hgather using 1
  funext i
  change masked B.threshold (Sum.elim (fun j=>strings K B (slot (e j))) T.reg (Caddy.e i)).support
    (Sum.elim (fun j=>WilsonVacuumPreResetCurvatureField.source K c γ β (e j)) T.E (Caddy.e i)) U=F (Caddy.e i)
  cases h:Caddy.e i <;> rfl

theorem rooted (simple:G.Simple)(hn:20<n.val)(A:Listing G n)(B:BudgetPoint)(K:PathData G)(c:Clip)
    {width paths Λ σ C:ℝ}(hc:K.Bounds c width paths Λ)
    (hs:0<σ)(hz:preExponent B/B.B≤σ/4)(blocks:2≤B.B)(γ β:ℝ)
    (Z:SeriesA G)(draw:Draw Z σ C)(grade:∀a∈Z,0<a.grade)(ρ θ:ℝ)(t q:ℕ)
    (U:Config G n)(quiet:flags B.threshold U=∅):
    let M:=source A B K c width paths γ β σ C Z (fun d v=>ρ*θ^(d+2-v)) t q
    ∑' i,masked B.threshold (M.listing.reg i).support (M.trunk i) U=
      ∑x:Site n,(γ*OriginalMarkedRunAction.secondAt c K x U+β*OriginalMarkedRunAction.interactionAt K x U+
        ρ*OriginalMarkedRunAction.springPacketsAt Z θ x U):=by
  intro M
  rw [(measured simple hn A B K c hc hs hz blocks γ β Z draw (fun d v=>ρ*θ^(d+2-v)) t q U).tsum_eq]
  rw [←(WilsonVacuumPreResetCurvatureField.original B K c hc γ β U).tsum_eq,
    WilsonVacuumPreResetCurvatureField.rooted B K c hc γ β U quiet,
    WilsonVacuumPreResetPeriodField.rooted simple hn B hs hz blocks Z draw grade ρ θ U quiet,Finset.sum_add_distrib]
  simp only [Finset.sum_add_distrib]

end YM.Integration.WilsonVacuumPreResetModelBoard
