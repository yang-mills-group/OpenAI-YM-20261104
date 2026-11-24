import YM.Integration.WilsonIndependentCollarOrdinaryCruise

/-! Unweighted angular cost at a genuine pinned public position, uniform
in the length of the full Wilson optical collar. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrdinaryWeak
open Function Filter Finset Lattice Wilson RG Precision
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Winding
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonReceivedFixedDigitHistory WilsonIndependentCollarOrdinaryCruise
open scoped BigOperators Classical
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e:ℕ}

abbrev price (G:Gauge) (k e:ℕ):Credit:=(bulkCert G k e 0 Credit.leanC Credit.leanC).choose

/-- One universal inlet norm suffices for all actual dual measurements.
The returned bound sums the absolute values over the entire angular tuple. -/
theorem scalar (Q:Realm G (e+1) Credit.leanC) (N:ℕ) (cells:Digits Q.draws ι)
    (seed:Outerm G D) (well:Wellness k seed) (S:Finset ι) (days m:ℕ) (y:ι → Cover)
    (hm:Q.anchor ≤ m) (cut:m+days≤N) (Z A:ℝ) (room:PadRank Q m (m+days) Z) (pos:0≤A)
    (dorm:Dormitory Q (mass k S) 0 Credit.leanC) (f:Pen D S →L[ℝ] ℝ)
    (input:Saturation e 0 0 (tuftV f (levelsO (seed (address Q.draws cells days m y)) S)).2 0 A)
    (q r:ℕ) (hq:q≤e):
    Fruit 0 0 0 ((tuftV f (levelsO (itinerary Q.draws Q.paid k N cells days m seed y) S)).2 q r)
      ((price G (mass k S) e).buy Z*A):=by
  let walk:Escort Q m (m+days) (fun _=>0):=⟨hm,by omega,by intros;norm_num,by intros;norm_num,
    by intro i _ _;simp [thinLevel]⟩
  rw [WilsonIndependentCollarOrdinaryCruise.original Q.draws Q.paid Q.hG Q.green N cells seed well
    S f days m y cut]
  exact (bulkCert G (mass k S) e 0 Credit.leanC Credit.leanC).choose_spec q hq r Q dorm
    m (m+days) _ N Z walk room cut _ A
      ((placedO _ (well.level' _) S).tuft f) pos input

/-- Hahn--Banach is used at one mode at a time. This gives an operator
bound over all marks and profiles without an absolute sum of suprema. -/
theorem original (Q:Realm G (e+1) Credit.leanC) (N:ℕ) (cells:Digits Q.draws ι)
    (seed:Outerm G D) (well:Wellness k seed) (S:Finset ι) (days m:ℕ) (y:ι → Cover)
    (hm:Q.anchor ≤ m) (cut:m+days≤N) (Z A:ℝ) (room:PadRank Q m (m+days) Z) (pos:0≤A)
    (dorm:Dormitory Q (mass k S) 0 Credit.leanC)
    (input:∀f:Pen D S →L[ℝ] ℝ,‖f‖≤1 →
      Saturation e 0 0 (tuftV f (levelsO (seed (address Q.draws cells days m y)) S)).2 0 A)
    (q r:ℕ) (hq:q≤e):
    Wig Bank.terrain y 0 ((price G (mass k S) e).buy Z*A) S
      ((levelsO (itinerary Q.draws Q.paid k N cells days m seed y) S).2 q r):=by
  have hZ:1≤Z:=(Q.depth m hm).trans (room.year m le_rfl (by omega))
  refine ⟨mul_nonneg (zero_le_one.trans (Credit.purchase _ hZ)) pos,?_⟩
  intro x
  let X:=(levelsO (itinerary Q.draws Q.paid k N cells days m seed y) S).2 q r x
  obtain ⟨f,unit,exactly⟩:=exists_dual_vector'' ℝ X
  change f X=‖X‖ at exactly
  have earn:=scalar Q N cells seed well S days m y hm cut Z A room pos dorm f (input f unit) q r hq
  have paid:‖f X‖≤(price G (mass k S) e).buy Z*A:=by
    have pay:SumBudget (fun x=>hedge 0 0 0 x*
      ‖(tuftV f (levelsO (itinerary Q.draws Q.paid k N cells days m seed y) S)).2 q r x‖)
      ((price G (mass k S) e).buy Z*A):=earn
    have h:=(pay.2.1.le_tsum x (fun j _=>pay.1 j)).trans pay.2.2
    simpa only [hedge,autumn,pow_zero,one_mul,tuftV,ply_v,ContinuousLinearMap.coe_coe,X] using h
  rw [exactly,Real.norm_of_nonneg (norm_nonneg _)] at paid
  simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using paid

end YM.Integration.WilsonIndependentCollarOrdinaryWeak
end
