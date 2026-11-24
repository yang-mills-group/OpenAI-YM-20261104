import YM.Integration.WilsonMaxwellThermometerNominatedAlgebra

/-! Source amplitudes follow their own marked faces through every finite
conditional update, including its shared entering quiet action and reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedTrajectory
open Function Lattice RG Wilson Precision Tree Laurent
open FormalBulk08 Flat Mesa Next.Free
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonMaxwellThermometerNominatedAlgebra
open scoped Classical BigOperators

variable {G:Gauge} {I U V W:Type} [DecidableEq I] {D:I→ℕ}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem character (t:ℝ) (P:Era G V) :
    tuftV (t • ContinuousLinearMap.id ℝ V) P=t • P := by
  apply Prod.ext <;> rfl

theorem currency (t:ℝ) (L:V→L[ℝ]W) (P:Era G V) :
    tuftV L (t • P)=t • tuftV L P := by
  apply Prod.ext
  · funext n
    exact (ply L.toLinearMap).map_smul t (P.1 n)
  · exact (ply L.toLinearMap).map_smul t P.2

theorem propagates [CompleteSpace V] (A:Levels G) (Ñ:ChartRatio G) {m N k:ℕ}
    (live:m<N) (simple:G.Simple) (ratio:LocalRatio Ñ) (P:Era G V) (valid:Auth k P) (t:ℝ) :
    verseI A Ñ m N k (t • P)=t • verseI A Ñ m N k P := by
  rw [←character t P,←character t (verseI A Ñ m N k P)]
  exact (ply_verse A live simple ratio valid (t • ContinuousLinearMap.id ℝ V)).symm

theorem step (A:Levels G) (Ñ:ChartRatio G) {m N:ℕ} (k:I→ℕ)
    (live:m<N) (simple:G.Simple) (ratio:LocalRatio Ñ)
    (M:family G D) (valid:Eu k M) (h:I→ℝ) :
    logO A Ñ m N (scaled h M) k=scaled h (logO A Ñ m N M k) := by
  have paid : edV A Ñ m N (scaled h M) k=scaled h (edV A Ñ m N M k) := by
    funext S
    change verseI A Ñ m N (mass k S) (levelsO (scaled h M) S)=
      pay h S • verseI A Ñ m N (mass k S) (levelsO M S)
    rw [exponential,propagates A Ñ live simple ratio _ (placedO M valid S)]
  funext S
  unfold logO
  rw [paid]
  exact logarithm h _ S

theorem sums (P:Patch) (K:I→ℕ) (bank:Outerm G D) (h:I→ℝ) (x:I → Cover) (S:Finset I) :
    unite P K (fun y=>scaled h (bank y)) x S=pay h S • unite P K bank x S := by
  unfold unite
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  unfold portV
  change scalesK P K S • tuftV _ (pay h S • bank (splitQ P x S y) S)=_
  rw [currency,smul_comm (scalesK P K S) (pay h S)]

theorem history (A:Levels G) (Ñ:ChartRatio G) (K k:I→ℕ) (N b:ℕ) (upper:b≤N)
    (simple:G.Simple) (ratio:LocalRatio Ñ) (seed:Outerm G D) (valid:Wellness k seed)
    (h:I→ℝ) {j:ℕ} (live:j≤b) (x:I → Cover) (S:Finset I) :
    Gears A Ñ K k N b j (fun y=>scaled h (seed y)) x S=
      pay h S • Gears A Ñ K k N b j seed x S := by
  obtain ⟨q,date⟩:=Nat.exists_eq_add_of_le live
  clear live
  induction q generalizing j x S with
  | zero =>
    have eq:j=b:=by omega
    subst j
    rw [gearTop,gearTop];rfl
  | succ q ih =>
    have earlier:j<b:=by omega
    have beyond:j+1≤b:=by omega
    let bank:=Gears A Ñ K k N b (j+1) seed
    have active:Wellness k bank:=Cog A Ñ upper seed valid simple ratio beyond
    have finer : Gears A Ñ K k N b (j+1) (fun y=>scaled h (seed y)) =
        fun y=>scaled h (bank y) := by
      funext y T
      exact ih (j:=j+1) y T (by omega)
    rw [gearUp A Ñ _ earlier,gearUp A Ñ _ earlier,finer]
    change unite (loose A j) K (fun y=>logO A Ñ j N (scaled h (bank y)) k) x S=
      pay h S • unite (loose A j) K (fun y=>logO A Ñ j N (bank y) k) x S
    have joined : (fun y=>logO A Ñ j N (scaled h (bank y)) k) =
        fun y=>scaled h (logO A Ñ j N (bank y) k) :=
      funext fun y=>step A Ñ k (earlier.trans_le upper) simple ratio (bank y) (active.level' y) h
    rw [joined,sums]

end YM.Integration.WilsonMaxwellThermometerNominatedTrajectory
