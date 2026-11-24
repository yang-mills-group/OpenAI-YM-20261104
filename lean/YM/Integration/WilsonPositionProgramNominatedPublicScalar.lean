import YM.Integration.WilsonPositionProgramNominatedWinding
import YM.Integration.WilsonMarkedIndependentMixedOrderedWinding

/-! On the same numerical fields, choose the internal cutoff first. The
finite-period hearing then approaches the actual occupied public Mer value
uniformly in the physical source cutoff and period. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramNominatedPublicScalar
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Fountain
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Winding WilsonCoeffUV.Layout WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops WilsonPositionProgramThermometerCoordinates
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNominatedRoster (selected)
open WilsonPositionProgramNominatedWinding (output unitFare)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{a e k u D:ℕ}

def finite (R:Run G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)(m top per t D:ℕ)
    (φ:Wilt (deck (G:=G) l d fit))(X:Herit (deck (G:=G) l d fit))(i:Alma ((primes G).F 0)):ℝ:=
  ((output R l d fit m m top D φ X).1 (R.family.side m per) t 0
    (slideC (R.family.side m per) Fin.elim0)) (brow ((primes G).F 0) i D)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(child:Fin (a+1)→Fin 3)(d:Fin (a+1)→ℕ)(fit:∀i,levels (child i)<d i)
    (cap:capP (deck (G:=G) (levels ∘ child) d fit) ≤ k)(δ η:ℝ)(pos:0<η)
    (income:WilsonPositionProgramUniformWindingTable.Complete R (levels ∘ child) d fit e unitFare δ):
    let Q:=deck (G:=G) (levels ∘ child) d fit
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1 ≤ zz L m →
    ∀A:Group R.family 6,A.station.k=m → A.station.checked f H A.horizon →
    ∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(Z:ℝ)(B:Fin (a+1)→ℝ)(ε:ℝ),0<ε →
    ∃K:ℕ,m ≤ K ∧ ∀φ:Wilt Q,Compar L.S (zz L) m m ≤ Z → Bough Q φ 1 Z B →
      (∀i j,i≠j → ClearDay (φ i) (φ j) (δ*longLog L m+14)) →
      ∀ᶠ p:ℕ in atTop,∀(N per n:ℕ),m < N → K ≤ n → ∀t:Fin (e+1),∀i:Alma ((primes G).F 0),
      let X:=selected R child d fit A m N per phase
      let fixed:=PowerSeries.coeff t.val (lodgeIn L R.metals.O ((primes G).T 0) big φ
        (normalized L R.metals.O Q X m) m m m k i)
      ‖finite R (levels ∘ child) d fit m n p t D φ X i-fixed‖<ε:=by
  intro Q L
  filter_upwards [WilsonPositionProgramNominatedWinding.original (f:=f) (H:=H) R simple v paid child d fit δ η pos income,
    WilsonPositionProgramNominatedReporter.original (f:=f) (H:=H) R simple v paid big rails child d fit cap η pos] with m winding reporter
  obtain ⟨s,hs,hear⟩:=winding m le_rfl
  intro clock A date checked phase Z B ε tol
  have half:0<ε/2:=half_pos tol
  obtain ⟨K,mK,stopped⟩:=reporter clock A date checked phase Z B (ε/2) half
  refine ⟨K,mK,?_⟩
  intro φ room shape clear
  let E:=(primes G).F 0
  have each (t:Fin (e+1))(i:Alma E):∀ᶠ p:ℕ in atTop,∀N per n:ℕ,m < N → K ≤ n →
      let X:=selected R child d fit A m N per phase
      let fixed:=PowerSeries.coeff t.val (lodgeIn L R.metals.O ((primes G).T 0) big φ
        (normalized L R.metals.O Q X m) m m m k i)
      ‖finite R (levels ∘ child) d fit m n p t D φ X i-fixed‖<ε:=by
    have ht:t.val≤e:=Nat.le_of_lt_succ t.isLt
    obtain ⟨C,_,sale⟩:=hear A date checked phase φ clear D t 0 ht Fin.elim0
    let w:=brow E i D
    have decay:Tendsto (fun p=>C*‖w‖*catchW s (R.family.side m p)) atTop (𝓝 0):=by
      simpa using (WilsonMarkedIndependentMixedOrderedWinding.disappears R s hs (b:=m)).const_mul (C*‖w‖)
    filter_upwards [sale,decay (Iio_mem_nhds half)] with p sold small
    intro N per n late enough X fixed
    let Y:=output R (levels ∘ child) d fit m m n D φ X
    let finiteRead:=Y.1 (R.family.side m p) t.val 0 (slideC (R.family.side m p) Fin.elim0)
    let coverRead:=Y.2 t.val 0 Fin.elim0
    have difference:‖finiteRead w-coverRead w‖≤(C*‖w‖)*catchW s (R.family.side m p):=by
      calc
        ‖finiteRead w-coverRead w‖=‖(finiteRead-coverRead) w‖:=rfl
        _ ≤ ‖finiteRead-coverRead‖*‖w‖:=(finiteRead-coverRead).le_opNorm w
        _ ≤ (C*catchW s (R.family.side m p))*‖w‖:=mul_le_mul_of_nonneg_right
          (sold N per n late (mK.trans enough)) (norm_nonneg _)
        _ = _:=by ring
    have anchored:‖coverRead w-fixed‖<ε/2:=by
      have near:=(stopped N per late n enough φ room shape t ht i).2
      have certificate:=WilsonPositionProgramReportedUnit.original L R.metals.O ((primes G).T 0)
        big φ (normalized L R.metals.O Q X m n) m n k t i
      have summed:=WilsonPositionProgramReportedCell.original L R.metals.O ((primes G).T 0)
        big φ (normalized L R.metals.O Q X m n) m n k t i
      exact (congrArg (fun x:ℝ=>‖x-fixed‖) (certificate.symm.trans summed)).trans_lt near
    calc
      ‖finiteRead w-fixed‖≤‖finiteRead w-coverRead w‖+‖coverRead w-fixed‖:=norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε :=by linarith [difference.trans_lt (show (C*‖w‖)*catchW s (R.family.side m p)<ε/2 from small)]
  filter_upwards [eventually_all.mpr (fun t=>eventually_all.mpr (each t))] with p received
  exact fun N per n h enough t i=>received t i N per n h enough

end YM.Integration.WilsonPositionProgramNominatedPublicScalar
end
