import YM.Integration.WilsonMarkedIndependentNormalizedElection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentReporterMove
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge} {e a:ℕ} {H:Hol G} {E W V C:Credit}

private def orient (L:Levels G)(O:ChartRatio G)(P:SealR G)(N b:ℕ)
    (X:P.Rider):P.Rider:=
  fun i=>∑j,(Wray L O P.ans P.path N b i j) • X j

private theorem orient_inverse (L:Levels G)(O:ChartRatio G)(P:SealR G)(N b:ℕ)
    (ok:IsUnit (Wray L O P.ans P.path N b).det)(X:P.Rider):
    PermuteLens L O P N b (orient L O P N b X)=X:=by
  let M:=Wray L O P.ans P.path N b
  funext i
  change (∑j,M⁻¹ i j • (∑k,M j k • X k)) = X i
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_smul,←Matrix.mul_apply]
  rw [Matrix.nonsing_inv_mul M ok]
  simp [Matrix.one_apply]

/-- The report at the earlier date carries the original short chronological transfer. -/
def moved (L:Levels G)(O:ChartRatio G)(P:SealR G)(N b m:ℕ)(X:P.Rider):P.Rider:=
  orient L O P N b (street L O P.ans P.path N b (m-b) (PermuteLens L O P N m X))

theorem top (P:SealR G)(A:Theatre H P.ans P.path e E W)(b m N:ℕ)
    (live:A.V.anchor ≤ b)(bm:b ≤ m)(mN:m ≤ N)(X:P.Rider):
    let L:=A.V.draws
    let O:=A.V.paid
    centralL L O N b N P (PermuteLens L O P N b (moved L O P N b m X))=
      centralL L O N m N P (PermuteLens L O P N m X):=by
  intro L O
  have unit:IsUnit (Wray L O P.ans P.path N b).det:=
    wick_unit _ (production A (bm.trans mN) live).1 _ _
  rw [moved,orient_inverse L O P N b unit]
  have r := Street_refund (N := N) (m := b) (i := m-b) (j := N-m) A (PermuteLens L O P N m X) live (by omega)
  rw [show b + (m-b) = m by omega,show m-b + (N-m) = N-b by omega] at r
  exact congrArg (Shrine (Peaks L O P.ans P.path N N)) r

theorem enrolled (R:Realm G (e+1) E)(Q:Fin (a+1)→SealR G)(F:FramesR H R W V Q C)
    (b m N:ℕ)(live:R.anchor ≤ b)(bm:b ≤ m)(mN:m ≤ N)(X:Herit Q):
    let L:=R.draws
    let O:=R.paid
    coatA L O N b Q (fun i=>PermuteLens L O (Q i) N b (moved L O (Q i) N b m (X i)))=
      coatA L O N m Q (fun i=>PermuteLens L O (Q i) N m (X i)):=by
  intro L O
  have h (i):centralL L O N b N (Q i) (PermuteLens L O (Q i) N b (moved L O (Q i) N b m (X i)))=
      centralL L O N m N (Q i) (PermuteLens L O (Q i) N m (X i)):=by
    obtain ⟨U⟩:=F i
    dsimp only [L,O]
    rw [←U.p.lands,←U.p.modes]
    exact top (Q i) U.p.f.arch b m N (U.p.tap.symm ▸ live) bm mN (X i)
  funext y I
  by_cases hi:I.card=1
  · obtain ⟨i,rfl⟩:=Finset.card_eq_one.mp hi
    rw [coatLeaf,coatLeaf,h]
  · simp [coatA,hi]

end YM.Integration.WilsonMarkedIndependentReporterMove
