import YM.Integration.WilsonVacuumPreResetLiftedPiece

/-! The before-volume lifted path tail for the whole genuinely rendered
period action. The cutoff reads each incoming atom's actual lifted path
length, including its two-leg clover correction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedSeries
open Function Finset Lattice RG Marker Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render PhysicalNext PhysicalNext.Repeat IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Push.AbsoluteSums
open WilsonVacuumPreResetPeriodEntries WilsonVacuumPreResetLiftedPiece
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

def length (n:Side):SeriesA G → ℕ → ℕ
  | [],_=>0
  | a::l,i=>(Payload.coding i).elim (length n l) (fun j=>(a.cells ((numbering (Cycle n)) j).2).length)

def cut (n:Side)(D:ℕ)(k:ℕ→ℕ→ℝ):SeriesA G→ Activities G n
  | []=>Pane.pale n G
  | a::l=>(issue n a (postW a.cells D)).attach (k a.grade (a.rise+2)) (cut n D k l)

theorem listing (n:Side)(B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(D:ℕ)(k:ℕ→ℕ→ℝ):
    (cut n D k Z).reg=(entries n B σ C Z k).reg:=by
  induction Z with
  | nil=>rfl
  | cons a l ih=>
    funext i
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    cases j with
    | inl j=>simpa [cut,entries,tally,IterationFour.Vacuum.Render.adorn,Payload.attach] using congrFun ih j
    | inr j=>
      simpa [cut,entries,tally,IterationFour.Vacuum.Render.adorn,Payload.attach] using congrFun
        ((labels n a (postW a.cells D)).trans (congrArg Payload.labels (whole n a B σ C))) j

theorem selected (n:Side)(B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(D:ℕ)(k:ℕ→ℕ→ℝ)(i:ℕ):
    (cut n D k Z).E i=if D≤length n Z i then (entries n B σ C Z k).E i else 0:=by
  induction Z generalizing i with
  | nil=>simp [cut,entries,tally,IterationFour.Vacuum.Render.adorn,Pane.pale]
  | cons a l ih=>
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    cases j with
    | inl j=>simpa [cut,entries,tally,length,IterationFour.Vacuum.Render.adorn,Payload.attach] using ih j
    | inr j=>
      simp only [cut,entries,tally,List.map_cons,IterationFour.Vacuum.Render.adorn,length,Payload.attach,
        Function.comp_apply,Equiv.apply_symm_apply,Sum.elim_inr,Pi.smul_apply]
      rw [fields,whole n a B σ C]
      unfold postW
      split_ifs <;> simp [FundedCorrectedPeriod.piece]

private theorem paid (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:B.supportExponent/B.B≤σ/4)(blocks:2≤B.B)(Z:SeriesA G)(draw:Draw Z σ C)(D:ℕ)(k:ℕ→ℕ→ℝ):
    (cut n D k Z).Valid B (rebate σ D *quote (Z.map (FundedCorrectedPeriod.piece n B σ C)) k) 0:=by
  induction Z with
  | nil=>simpa [cut,quote,IterationFour.Vacuum.Render.dollars] using Pane.whey n G B
  | cons a l ih=>
    have tail:=ih ⟨draw.1,fun z hz=>draw.2 z (List.mem_cons_of_mem a hz)⟩
    have head:=WilsonVacuumPreResetLiftedPiece.long simple hn B hs reach blocks a (draw.2 a List.mem_cons_self) D
    have h:=Payload.payment (k a.grade (a.rise+2)) head tail
    convert h using 1
    · rfl
    change rebate σ D * (_ + _) = _ + _
    dsimp [FundedCorrectedPeriod.piece,quote]
    ring

theorem original (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:preExponent B/B.B≤σ/4)(blocks:2≤B.B)(Z:SeriesA G)(draw:Draw Z σ C)(D:ℕ)(k:ℕ→ℕ→ℝ):
    let A:=entries n B σ C Z k
    let Q:=quote (Z.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)) k
    Meadow.Budget B A.reg (fun i=>if D≤length n Z i then A.E i else 0) (rebate σ D*Q):=by
  intro A Q
  have h:=paid simple hn (Song.headline B) hs reach blocks Z draw D k
  obtain ⟨f,charges,anchor⟩:=h.boundE
  have relabel:(cut n D k Z).reg=A.reg:=listing n B σ C Z D k
  have refield:(cut n D k Z).E=(fun i=>if D≤length n Z i then A.E i else 0):=
    funext (selected n B σ C Z D k)
  rw [←relabel,←refield]
  refine ⟨f,Song.enhanced B _ _ _ anchor,fun i=>?_⟩
  have t:=h.regular.smooth i
  exact ⟨⟨t.sites,t.borel,t.symmetry,t.smooth,t.hasDerivs⟩,charges i⟩

end YM.Integration.WilsonVacuumPreResetLiftedSeries
