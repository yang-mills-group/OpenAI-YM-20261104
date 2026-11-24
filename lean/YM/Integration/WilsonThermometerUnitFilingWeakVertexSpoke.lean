import YM.Integration.WilsonThermometerUnitFilingWeakJoin

/-! A contracted leg of the actual covered upper vacuum with the selected finite-torus covariance. Both budgets precede the cutoff and the period. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakVertexSpoke
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding Next.Free Work.F08 FormalBulk08 Flat Stationary
open WilsonOriginalCompoundStrip WilsonThermometerUnitFilingWeakJoin
open scoped Classical BigOperators
variable {G:Gauge}

theorem original (Q:Request G)(R:Run G)(simple:G.Simple)
    (fund:WilsonOriginalCompoundLodge.Filed R.kit)(source:FundedMarkedCoverRows.prices (fun _ _=>0) R.kit)(e:ℕ):
    ∀ᶠ first:ℕ in atTop,∃ V:Realm G (e+1) Credit.leanC,V.draws=R.family.path.levels ∧ V.paid=R.metals.O ∧
      V.anchor=first ∧ ∀i,V.anchor ≤ i+1 → 4 ≤ R.alloy.B.a.clock.J i → ∀H,
      let L:=R.alloy.B.a
      let K:=R.metals.p.kernel
      let X:Patch:=(L.clock.op i 0).patch
      let s:=(WilsonThermometerUnitFilingWeakRoom.book G K X.J (L.clock.J i)).width
      let μ:=WilsonThermometerUnitFilingWeakStrip.trial (WilsonOriginalCompoundVertexStrip.narrowed Q)
        K (L.clock.J (i+1)) H
      ∀F:Lodge X,∃c:ℝ,0<c ∧ c ≤ Borough.ageZ (L.clock.hatBeta i) ∧ ∀N M:ℕ,i+1 ≤ N → N ≤ M →
      ∀h:X.Branches K G,∀n:Side,
        let P:=destination L N i
        let Γ:=Flat.gamma G K P F h
        ∀t:ℝ,0 ≤ t → t ≤ min μ (s/(P.L.val:ℝ)) → ∀x o inc:Cover,∀a b,∀ξ:Hooks G,∀grade (hg:grade ≤ e+1) k,
          let offset:=lift b.val.1+inc
          ∑y:Site n,|Γ.acts n (wrap n x,a) (y,b)| *
            vertex n P.L x offset o t ξ (actionW L R.metals.O N (i+1) grade (k+1)) y ≤
          c*(Real.exp (t*size (stretch P.L x+offset-o))*
            (WilsonOriginalCompoundVertex.tariff G e grade k 0 hg).buy (Borough.ageZ (L.clock.hatBeta (i+1)))):=by
  filter_upwards [WilsonThermometerUnitFilingWeakTrunk.original Q R simple _ source e] with first enrolled
  obtain ⟨V,draws,coins,anchor,stock⟩:=enrolled
  refine ⟨V,draws,coins,anchor,?_⟩
  intro i hi tall H L K X s μ F
  obtain ⟨c,cp,en,rows⟩:=WilsonOriginalCompoundLodge.figure R fund i tall F
  refine ⟨c,cp,en,?_⟩
  intro N M upper next h n P A t tp room x o inc a b ξ grade hg k d
  have lp:0<(P.L.val:ℝ):=by positivity
  obtain ⟨tf,ts⟩:=le_min_iff.mp room
  have answer:=stock (i+1) hi H grade hg k N upper t tp tf
  have flat:=stock (i+1) hi H grade hg k N upper 0 le_rfl (le_trans tp tf) (o,ξ) o
  have pos:= (tsum_nonneg flat.1).trans flat.2.2
  simp only [zero_mul,Real.exp_zero,one_mul] at pos
  exact priced A n P.L x d o a b ξ _ (rows N M upper next h).1 pos tp
    ((le_div_iff₀ lp).mp ts) (fun z=>answer (z,ξ) o)

end YM.Integration.WilsonThermometerUnitFilingWeakVertexSpoke
