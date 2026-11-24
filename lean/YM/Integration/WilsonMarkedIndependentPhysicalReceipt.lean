import YM.Integration.WilsonMarkedIndependentOnePeriod
import YM.Integration.WilsonDepositedFreshFiniteHistory

/-! An authentic deposited bank and a genuinely fresh parent on the same torus history.
Only the initial fine side carries an outstanding positive-degree quiet input. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedIndependentPhysicalReceipt
open Function Finset Wilson Lattice Source Labels RG Precision Marker
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Winding
open IndependentSourcePathFamily WilsonFiniteMarkedHistoryStep
open scoped Classical BigOperators

variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ}
  {I F : ι → Type} [∀ i,Fintype (I i)] [∀ i,Fintype (F i)] {e : ℕ}

open WilsonDepositedFreshFiniteHistory (bank enter lawful source)
open WilsonMarkedIndependentOnePeriod (Course)
open WilsonMarkedIndependentPhysicalIntake (PositiveAt PairedAt narrow)

theorem original (Q : Realm G (e+1) Credit.leanC) (K : ι → ℕ) (m b : ℕ)
    (hm : Q.anchor ≤ m) (mb : m ≤ b) (old : Finset ι)
    (X : ∀ i,I i → Seed G (D i)) (Y : ∀ i,F i → Seed G (D i))
    (hX : ∀ i a,(X i a).rank ≤ k i+(X i a).head)
    (hY : ∀ i a,(Y i a).rank ≤ k i+(Y i a).head) {s : ℝ} (hs : 0<s) :
    ∃ (d : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, b<N → ∀ (P : Course Q.draws) (V : ℝ), 1 ≤ V →
      PositiveAt Q.draws Q.paid e N (b+1) (P.side (b+1)) s V →
      PairedAt e (Gears Q.draws Q.paid K k N b m (bank (k:=k) Q K N b old X Y)) (P.side m) σ (C*V^d) := by
  obtain ⟨A,hA,first⟩ := source (e:=e) X hX hs
  obtain ⟨u,C,t,hC,ht,prior⟩ :=
    WilsonMarkedIndependentOnePeriod.original (D:=D) (k:=k) Q K b (b+1) (hm.trans mb) (Nat.le_succ _) hs
  obtain ⟨Ffee,hF,fresh⟩ := source (e:=e) Y hY ht
  let M := max A Ffee
  let H := C*M
  have hM : 1 ≤ M := hA.trans (le_max_left ..)
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hC hM
  obtain ⟨p,B,σ,hB,hσ,roll⟩ := WilsonMarkedIndependentOnePeriod.original (D:=D) (k:=k) Q K m b hm mb ht
  refine ⟨u*(p+1),B*H^(p+1),σ,one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hH),hσ,?_⟩
  intro N cut P V hV previous
  have hot := one_le_pow₀ (n:=u) hV
  let W := H*V^u
  have hW : 1 ≤ W := one_le_mul_of_one_le_of_one_le hH hot
  let x := Gears Q.draws Q.paid K k N (b+1) b (independent X)
  have laws := (OriginalCoverReanchoring.iterated X Q.draws Q.paid K (Nat.le_succ b) cut
    Q.hG Q.green hX).1
  have birth := (OriginalCoverReanchoring.deposited X hX).1
  obtain ⟨quiet,active⟩ := prior N cut P (independent X) birth V A hV hA previous (first (P.side (b+1)))
  have less : C*V^u≤W := by
    calc _ ≤ C*V^u*M := le_mul_of_one_le_right (by positivity) hM
         _ = _ := by dsimp [W,H]; ring
  have left : C*V^u*A ≤ W := by
    calc _ ≤ C*V^u*M := mul_le_mul_of_nonneg_left (le_max_left ..) (by positivity)
         _ = _ := by dsimp [W,H]; ring
  have right : Ffee ≤ W := (le_max_right A Ffee).trans
    ((le_mul_of_one_le_left (zero_le_one.trans hM) hC).trans
       (le_mul_of_one_le_right (zero_le_one.trans hH) hot))
  have entered : PairedAt e (bank (k:=k) Q K N b old X Y) (P.side b) t W := by
    intro z S i hi l
    by_cases keep : S ⊆ old
    · simpa only [bank,enter,if_pos keep] using
        (narrow active le_rfl (by positivity) left z S i hi l)
    · simpa only [bank,enter,if_neg keep] using
        (narrow (fresh (P.side b)) le_rfl (zero_le_one.trans hF) right z S i hi l)
  have paid := (roll N (Nat.le_of_lt cut) P _ (lawful old laws (OriginalCoverReanchoring.deposited Y hY).1)
    W W hW hW (fun a ha hu l hl => (quiet a ha hu l hl).more less) entered).2
  have tariff : B*H^(p+1)*V^(u*(p+1)) = B*W^p*W := by
    dsimp [W]; rw [mul_pow,pow_mul]; simp only [pow_succ]; ring
  rw [tariff]
  exact paid

end YM.Integration.WilsonMarkedIndependentPhysicalReceipt
end
