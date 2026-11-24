import YM.Integration.WilsonFiniteMarkedHistory
import YM.Integration.WilsonRegisteredBareMarkedWinding
import YM.Integration.OriginalCoverReanchoring

/-! A deposited marked value and a fresh, separately positioned Wilson
path enter the same finite conditional logarithm on the next genuine date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonDepositedFreshFiniteHistory
open Function Finset Wilson Lattice Source Labels RG Precision Marker
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Winding
open IndependentSourcePathFamily WilsonFiniteMarkedHistoryStep
open scoped Classical BigOperators

variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ}
  {I F : ι → Type} [∀ i,Fintype (I i)] [∀ i,Fintype (F i)] {e : ℕ}

/-- The literal periodization of each registered bare source is priced at
all fine sites and finite sides. No divisibility restriction is needed. -/
theorem source (X : ∀ i,I i → Seed G (D i)) (hX : ∀ i b,(X i b).rank ≤ k i+(X i b).head)
    {s : ℝ} (hs : 0 < s) : ∃ A : ℝ, 1 ≤ A ∧ paired e (independent X) s A := by
  let u := 32*s
  have hu : 0 < u := by dsimp [u]; positivity
  let Z : Finset ι := univ
  let H := diamond G e (mass k Z) u
  let A := bill X k e (4*u)
  have hH : 1 ≤ H := diamond_nn G hu
  have base (p : ι → Cover) := preblock X (k:=k) p Z e (w:=4*u) (by positivity) hX
  have hA : 0 ≤ A := (base (fun _ => 0)).1
  refine ⟨max 1 (H*A),le_max_left ..,?_⟩
  intro n p S i hi l
  rw [WilsonRegisteredBareMarkedWinding.original X p hX S n i l]
  have pay : 0 ≤ (max 1 (H*A))^S.card := pow_nonneg (zero_le_one.trans (le_max_left ..)) _
  by_cases none : S=∅
  · subst S
    rw [empty X p]
    change MarkU p _ (plume 0 _) 0 _ _
    rw [plume_zero]
    exact MarkU.zero.more pay
  by_cases far : mass k Z+e < l
  · have size : mass k S ≤ mass k Z := by
      unfold mass; exact Finset.sum_le_sum_of_subset (subset_univ S)
    rw [((base p).2.1 S).coverN _ _ (by omega),plume_zero]
    exact MarkU.zero.more pay
  have live := nonempty_iff_ne_empty.mpr none
  have enough := (base p).2.2.2 S (subset_univ _) i hi l
  rw [show steep (4*u) = u by unfold steep; ring] at enough
  have entry := plumeW (n:=n) enough live hu
  rw [show u/32=s by dsimp [u]; ring] at entry
  refine entry.more ?_
  calc
    _ ≤ H*A^S.card := mul_le_mul_of_nonneg_right (wins (e:=e) (r:=mass k Z) G hu (by omega))
        (pow_nonneg hA _)
    _ ≤ (H*A)^S.card := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hH (Nat.ne_of_gt (card_pos.mpr live)))
        (pow_nonneg hA _)
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hH) hA) (le_max_right ..) _

def enter (old : Finset ι) (X Y : Outerm G D) : Outerm G D :=
  fun x S => if S ⊆ old then X x S else Y x S

omit [Fintype ι] in
theorem lawful (old : Finset ι) {X Y : Outerm G D} (hx : Wellness k X) (hy : Wellness k Y) :
    Wellness k (enter old X Y) := by
  refine ⟨fun x => ?_,fun x S => ?_,fun x y S agree => ?_⟩
  · simpa only [enter,empty_subset,if_true] using hx.quiet' x
  · by_cases keep : S ⊆ old
    · simpa only [enter,if_pos keep] using hx.level' x S
    · simpa only [enter,if_neg keep] using hy.level' x S
  · by_cases keep : S ⊆ old
    · simpa only [enter,if_pos keep] using hx.filial x y S agree
    · simpa only [enter,if_neg keep] using hy.filial x y S agree

/-- The first family has traversed the actual block at b. The second is
inserted immediately after that deposition, before the next conditional log. -/
def bank (Q : Realm G (e+1) Credit.leanC) (K : ι → ℕ) (N b : ℕ) (old : Finset ι)
    (X : ∀ i,I i → Seed G (D i)) (Y : ∀ i,F i → Seed G (D i)) : Outerm G D :=
  enter old (Gears Q.draws Q.paid K k N (b+1) b (independent X)) (independent Y)

theorem original (Q : Realm G (e+1) Credit.leanC) (K : ι → ℕ) (m b : ℕ)
    (hm : Q.anchor ≤ m) (mb : m ≤ b) (old : Finset ι)
    (X : ∀ i,I i → Seed G (D i)) (Y : ∀ i,F i → Seed G (D i))
    (hX : ∀ i a,(X i a).rank ≤ k i+(X i a).head)
    (hY : ∀ i a,(Y i a).rank ≤ k i+(Y i a).head) {s : ℝ} (hs : 0<s) :
    ∃ (d : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, b<N → ∀ V : ℝ, 1 ≤ V →
      WilsonFiniteVacuumWindingDate.positive Q.draws Q.paid e N (b+1) s V →
      paired e (Gears Q.draws Q.paid K k N b m (bank (k:=k) Q K N b old X Y)) σ (C*V^d) := by
  obtain ⟨A,hA,first⟩ := source (e:=e) X hX hs
  obtain ⟨u,C,t,hC,ht,prior⟩ :=
    WilsonFiniteMarkedHistory.original (D:=D) (k:=k) Q K b (b+1) (hm.trans mb) (Nat.le_succ _) hs
  obtain ⟨Ffee,hF,fresh⟩ := source (e:=e) Y hY ht
  let M := max A Ffee
  let H := C*M
  have hM : 1 ≤ M := hA.trans (le_max_left ..)
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hC hM
  obtain ⟨p,B,σ,hB,hσ,roll⟩ := WilsonFiniteMarkedHistory.original (D:=D) (k:=k) Q K m b hm mb ht
  refine ⟨u*(p+1),B*H^(p+1),σ,one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hH),hσ,?_⟩
  intro N cut V hV previous
  have hot := one_le_pow₀ (n:=u) hV
  let W := H*V^u
  have hW : 1 ≤ W := one_le_mul_of_one_le_of_one_le hH hot
  let x := Gears Q.draws Q.paid K k N (b+1) b (independent X)
  have laws := (OriginalCoverReanchoring.iterated X Q.draws Q.paid K (Nat.le_succ b) cut
    Q.hG Q.green hX).1
  have birth := (OriginalCoverReanchoring.deposited X hX).1
  obtain ⟨quiet,active⟩ := prior N cut (independent X) birth V A hV hA previous first
  have less : C*V^u≤W := by
    calc _ ≤ C*V^u*M := le_mul_of_one_le_right (by positivity) hM
         _ = _ := by dsimp [W,H]; ring
  have left : C*V^u*A ≤ W := by
    calc _ ≤ C*V^u*M := mul_le_mul_of_nonneg_left (le_max_left ..) (by positivity)
         _ = _ := by dsimp [W,H]; ring
  have right : Ffee ≤ W := (le_max_right A Ffee).trans
    ((le_mul_of_one_le_left (zero_le_one.trans hM) hC).trans
       (le_mul_of_one_le_right (zero_le_one.trans hH) hot))
  have entered : paired e (bank (k:=k) Q K N b old X Y) t W := by
    intro n z S i hi l
    by_cases keep : S ⊆ old
    · simpa only [bank,enter,if_pos keep] using
        (WilsonFiniteMarkedHistory.weaken active le_rfl (by positivity) left n z S i hi l)
    · simpa only [bank,enter,if_neg keep] using
        (WilsonFiniteMarkedHistory.weaken fresh le_rfl (zero_le_one.trans hF) right n z S i hi l)
  have paid := (roll N (Nat.le_of_lt cut) _ (lawful old laws (OriginalCoverReanchoring.deposited Y hY).1)
    W W hW hW (fun n a ha hu l hl => (quiet n a ha hu l hl).more less) entered).2
  have tariff : B*H^(p+1)*V^(u*(p+1)) = B*W^p*W := by
    dsimp [W]; rw [mul_pow,pow_mul]; simp only [pow_succ]; ring
  rw [tariff]
  exact paid

end YM.Integration.WilsonDepositedFreshFiniteHistory
