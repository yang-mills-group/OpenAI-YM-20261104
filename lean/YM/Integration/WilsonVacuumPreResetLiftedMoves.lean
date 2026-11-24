import YM.Integration.WilsonVacuumPreResetLiftedRack

/-! The genuine affine action on the original covering catalogue preserves
the raw path number and the finite lifted-length selection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedMoves
open Function Finset Set Lattice RG Marker Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render AnalyticBridge VerifiedReset Collection Quotes WilsonStartup
open RG01Estimate IterationFour.Vacuum Extra.Iteration Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Push.AbsoluteSums.Animals
open WilsonVacuumPreResetLiftedAgreement WilsonVacuumPreResetLiftedPiece WilsonVacuumPreResetLiftedSite
open WilsonVacuumPreResetPeriodEntries WilsonVacuumPreResetLiftedFolio
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}

open WilsonVacuumPreResetPeriodIndex WilsonVacuumPreResetPeriodCatalogue
open private packet join from YM.Integration.WilsonVacuumPreResetPeriodIndex

def flag (n:Side)(t q:ℕ):SeriesA G→ℕ→ℕ
  | [],_=>0
  | a::l,i=>(Payload.coding i).elim (flag n t q l) (fun j=>if (numbering (Cycle n) j).2∈legs a t q then 1 else 0)

theorem flagged (Z:SeriesA G)(t q i:ℕ):
    i∈WilsonVacuumPreResetLiftedFolio.selected n t q Z ↔ flag n t q Z i=1:=by
  induction Z generalizing i with
  | nil=>simp [WilsonVacuumPreResetLiftedFolio.selected,flag]
  | cons a l ih=>
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    cases j with
    | inl j=>simpa [WilsonVacuumPreResetLiftedFolio.selected,flag] using ih j
    | inr j=>simp [WilsonVacuumPreResetLiftedFolio.selected,flag,seats]

theorem traced (B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(k:ℕ→ℕ→ℝ)(t q:ℕ)(s:Signed)(b:Site n):
    let A:=entries n B σ C Z k
    Nonempty (Moving A.reg A.E (flag n t q Z) s b):=by
  induction Z with
  | nil=>
    let other:=((Pane.whey n G B).moves s b).some
    exact ⟨⟨⟨other.ep,other.reg_site,other.reg_support,fun i=>funext (other.valuesE i)⟩,fun _ _=>rfl⟩⟩
  | cons a l ih=>
    let P:=(FundedCorrectedPeriod.piece n B σ C a).packet
    let v j:=if (numbering (Cycle n) j).2∈legs a t q then 1 else 0
    let orig:Moving P.labels P.action (fun j=>(numbering (Cycle n) j).2) s b:=(packet B σ C a s b).some
    have keep:Moving P.labels P.action v s b:=⟨orig.mirror,by intro i nz;dsimp [v];rw [orig.tier i nz]⟩
    exact join (entries n B σ C l k) P (flag n t q l) v (k a.grade (a.rise+2)) s b ih.some keep

theorem moves (B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(k:ℕ→ℕ→ℝ)(t q:ℕ)(s:Signed)(b:Site n):
    let M:=WilsonVacuumPreResetLiftedRack.model n B σ C k Z t q
    Nonempty (Caddy.Mirrors M.listing.reg s b M.trunk) ∧
    Nonempty (Caddy.Mirrors M.listing.reg s b M.pioneers) ∧
    Nonempty (Caddy.Mirrors M.listing.reg s b (-(M.trunk-M.pioneers))):=by
  intro M
  let A:=entries n B σ C Z k
  let W:=(traced (n:=n) B σ C Z k t q s b).some
  let g:=W.mirror
  have eqs (i)(nz:A.E i≠0):g.walks i∈WilsonVacuumPreResetLiftedFolio.selected n t q Z ↔ i∈WilsonVacuumPreResetLiftedFolio.selected n t q Z:=by
    simp only [flagged]
    rw [W.tier i nz]
  have P (i):M.pioneers (g.walks i)=M.pioneers i ∘ pull s b:=by
    change submitted A (WilsonVacuumPreResetLiftedFolio.selected n t q Z) (g.walks i)=submitted A (WilsonVacuumPreResetLiftedFolio.selected n t q Z) i ∘ pull s b
    by_cases z:A.E i=0
    · have zz:A.E (g.walks i)=0:=(g.posts i).trans (by rw [z];rfl)
      simp only [submitted,z,zz,ite_self]
      rfl
    by_cases h:i∈WilsonVacuumPreResetLiftedFolio.selected n t q Z
    · simp only [submitted,(eqs i z).2 h,h,if_true]
      exact g.posts i
    · have h':g.walks i∉WilsonVacuumPreResetLiftedFolio.selected n t q Z:=fun hv=>h ((eqs i z).1 hv)
      simp only [submitted,h',h,if_false]
      rfl
  refine ⟨⟨g⟩,⟨⟨g.walks,g.hooks,g.hues,P⟩⟩,⟨⟨g.walks,g.hooks,g.hues,?_⟩⟩⟩
  intro i
  funext U
  change -((A.E (g.walks i) U)-(M.pioneers (g.walks i) U))= -((A.E i (pull s b U))-(M.pioneers i (pull s b U)))
  rw [congrFun (g.posts i) U,congrFun (P i) U]
  rfl


end YM.Integration.WilsonVacuumPreResetLiftedMoves
