import YM.Integration.WilsonVacuumPreResetLiftedFolio
import YM.Work.E08

/-! The same finite original indices used in the torus comparison are
housed at their printed root, including the clover on the rank-two arm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedRack
open Function Finset Set Lattice RG Marker Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render AnalyticBridge VerifiedReset Collection Quotes WilsonStartup
open RG01Estimate IterationFour.Vacuum Extra.Iteration Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Push.AbsoluteSums.Animals
open WilsonVacuumPreResetLiftedAgreement WilsonVacuumPreResetLiftedPiece WilsonVacuumPreResetLiftedSite
open WilsonVacuumPreResetPeriodEntries WilsonVacuumPreResetLiftedFolio
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}

private theorem footprint {d:ℕ}(a:Atom G d)(q:ℕ)(h:a.length≤q):
    a.footprint (0:Site n)⊆neighbors q 0:=by
  intro z hz
  obtain ⟨v,hv,rfl⟩:=mem_image.mp hz
  apply (neighbors_mem ..).mpr
  apply Work.E08.separation_box_add
  rcases mem_insert.mp hv with rfl|kept
  · simp [box_test]
  obtain ⟨i,_,hi⟩:=mem_biUnion.mp kept
  have leg:(a.leg i).length≤a.length:=Finset.single_le_sum (fun j _=>Nat.zero_le (a.leg j).length) (mem_univ i)
  exact reaches q _ (leg.trans h) hi

theorem piece (a:PrismA G)(B:BudgetPoint)(σ C:ℝ)(x:Site n)(s:Signed)(i q:ℕ)
    (room:4≤q)(h:(a.cells i).length≤q):
    ((FundedCorrectedPeriod.piece n B σ C a).packet.labels (index x s i)).support⊆neighbors q x:=by
  rw [←whole]
  let F:=frame n a Frame.full
  have base:F.footprint i⊆neighbors q 0:=by
    rcases a with ⟨d,r,hv,A⟩
    cases r with
    | zero=>
      intro z hz
      rcases mem_union.mp hz with hit|near
      · exact footprint (A i) q h hit
      · exact (neighbors_mem ..).mpr (((neighbors_mem ..).mp near).trans (by omega))
    | succ v=>exact footprint (A i) q h
  unfold issue index
  simp only [Function.comp_apply,Equiv.apply_symm_apply]
  change (F.footprint i).image (affine s x)⊆neighbors q x
  intro z hz
  obtain ⟨v,hv,rfl⟩:=mem_image.mp hz
  have hv':=(neighbors_mem ..).mp (base hv)
  apply (neighbors_mem ..).mpr
  have moved (z w:Site n):separation (affine s x z) (affine s x w)=separation z w:=by simp [affine]
  have motion:=moved 0 v
  have atZero:affine s x (0:Site n)=x:=by simp [affine]
  rwa [←motion,atZero] at hv'

theorem support (B:BudgetPoint)(σ C:ℝ)(k:ℕ→ℕ→ℝ)(Z:SeriesA G)(t q:ℕ)(room:4≤q):
    let A:=entries n B σ C Z k
    ∀i∈WilsonVacuumPreResetLiftedFolio.selected n t q Z,
      (A.reg i).support⊆neighbors q (A.reg i).site:=by
  induction Z with
  | nil=>simp [WilsonVacuumPreResetLiftedFolio.selected]
  | cons a tail ih=>
    intro A i hi
    obtain ⟨j,hj,rfl⟩:=mem_map.mp hi
    cases j with
    | inl j=>simpa [A,entries,tally,IterationFour.Vacuum.Render.adorn,Payload.attach] using ih j (by simpa using hj)
    | inr j=>
      have seated':j∈seats n a t q:=by simpa using hj
      obtain ⟨⟨⟨s,x⟩,i⟩,listed,rfl⟩:=mem_map.mp seated'
      have small:= (mem_filter.mp (mem_product.mp listed).2).2
      have covered:=piece a B σ C x s i q room small
      have hs:((FundedCorrectedPeriod.piece n B σ C a).packet.labels (index x s i)).support⊆
          neighbors q ((FundedCorrectedPeriod.piece n B σ C a).packet.labels (index x s i)).site:=by
        rw [WilsonVacuumPreResetLiftedSite.position]
        exact covered
      simpa [A,entries,tally,IterationFour.Vacuum.Render.adorn,Payload.attach,index] using hs

def model (n:Side)(B:BudgetPoint)(σ C:ℝ)(k:ℕ→ℕ→ℝ)(Z:SeriesA G)(t q:ℕ):Precise.Leads G n:=
  let A:=entries n B σ C Z k
  ⟨⟨A.reg,A.forced⟩,A.E,WilsonVacuumPreResetPeriodCatalogue.submitted A
    (WilsonVacuumPreResetLiftedFolio.selected n t q Z),
    quote (Z.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)) k⟩

def original (B:BudgetPoint)(σ C:ℝ)(k:ℕ→ℕ→ℝ)(Z:SeriesA G)(t q:ℕ)(room:4≤q):
    let M:=model n B σ C k Z t q
    Abacus.Rack M.listing q M.pioneers:=by
  let A:=entries n B σ C Z k
  exact ⟨WilsonVacuumPreResetLiftedFolio.selected n t q Z,fun i x=>if (A.reg i).site=x then 1 else 0,
    fun i h=>if_neg h,fun _ _=>by simp,fun _ _ _=>by split <;> norm_num,fun i hi x hx=>by
      have eq:(A.reg i).site=x:=by simpa using hx
      rw [←eq]
      exact support B σ C k Z t q room i hi⟩

end YM.Integration.WilsonVacuumPreResetLiftedRack
