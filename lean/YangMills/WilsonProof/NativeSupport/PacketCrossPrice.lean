import YangMills.WilsonProof.NativeSupport.PacketSeparation
import YangMills.WilsonProof.NativeSupport.CalibratedTerminal
import YangMills.WilsonProof.NativeSupport.TerminalGas
import YangMills.WilsonProof.NativeSupport.PacketFactor

/-! The entire expenditure for log coefficients crossing different translated
words, summed over packet subsets and actual terminal supports. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson Marker Extra.Trajectories
open scoped BigOperators Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] {n : Side}
local notation "Π₀" => Poly (Stock.census V)

private def occupied : Finset (Finset V) := univ.filter Finset.Nonempty
private def external (g : V → H) := (occupied (V:=V)).filter (fun T => ¬∃ j,T⊆fibre g j)

private theorem two_words (g : V → H) {T : Finset V} (used : T∈external g) : 2 ≤ (T.image g).card := by
  obtain ⟨i,hi⟩ := (mem_filter.mp (mem_filter.mp used).1).2
  have outside : ¬T⊆fibre g (g i) := fun inc => (mem_filter.mp used).2 ⟨_,inc⟩
  obtain ⟨j,hj,ne⟩:=Finset.not_subset.mp outside
  exact one_lt_card.mpr ⟨g i,mem_image_of_mem g hi,g j,mem_image_of_mem g hj,
    fun eq => ne (mem_filter.mpr ⟨mem_univ j,eq.symm⟩)⟩

omit [Fintype H] [DecidableEq H] in
private theorem root_sum (B : Π₀) (i : V) (ρ : ℝ) :
    (∑ T∈univ.filter (fun T : Finset V => i∈T),ρ^T.card*‖B.part (tag T)‖)=
    ∑ s∈univ.filter (fun s : (Stock.census V).Mode => i∈s.val),Poly.toll (fun _=>ρ) s*‖B.part s‖ := by
  refine sum_bij' (fun T _=>tag T) (fun s _=>s.val) ?_ ?_ (fun _ _=>rfl) (fun _ _=>rfl) ?_
  · exact fun T ht=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ht).2⟩
  · exact fun s hs=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hs).2⟩
  intro T _
  simp [Poly.toll,tag]

private theorem cross_bill (g : V → H) (o : V → Site n) (distinct : Injective o) (m M L : ℕ)
    (fibres : ∀ j,(fibre g j).card ≤ m)
    (apart : ∀ i j,g i≠g j → 2*M+4*(2*M+1)*L<separation (o i) (o j))
    (pos : 0<L) {A D ρ a : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (radius : Real.exp (-A) ≤ ρ) (exponent : 1 ≤ a) (paid : m*A+D ≤ L)
    (C : Support n → Π₀) (home : ∀ Z s,(C Z).part s≠0 → s.val.image o⊆Z)
    (wallet : ∀ i : V,∑ Z : Support n,(∑ s∈univ.filter (fun s : (Stock.census V).Mode => i∈s.val),
      Poly.toll (fun _=>ρ) s*‖(C Z).part s‖)*Real.exp (a*coverNumber M Z) ≤ 1) :
    ∑ T∈external g,‖(∑ Z,C Z).part (tag T)‖ ≤ (Fintype.card V:ℝ)*Real.exp (-2*D) := by
  let K:=external g
  let cost (T : Finset V):=‖(∑ Z,C Z).part (tag T)‖
  let tariff (Z : Support n) (T : Finset V):=ρ^T.card*‖(C Z).part (tag T)‖
  let weight (Z : Support n):=Real.exp (a*coverNumber M Z)
  let e:=Real.exp (-2*D)
  have hr : 0 ≤ ρ := (Real.exp_pos _).le.trans radius
  have piece (T : Finset V) (ht : T∈K) : cost T ≤ e*∑ Z,tariff Z T*weight Z := by
    unfold cost
    rw [Poly.part_sum,Finset.mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun Z _=> ?_)
    by_cases zero : (C Z).part (tag T)=0
    · simp [tariff,zero]
    have localBill:=mode_payment g o distinct m M L fibres apart pos hA hD radius exponent paid T Z
      (home Z (tag T) zero) (two_words g ht)
    calc
      _ = 1*‖(C Z).part (tag T)‖ := (one_mul _).symm
      _ ≤ _ := (mul_le_mul_of_nonneg_right localBill (norm_nonneg _)).trans_eq (by dsimp [e,tariff,weight]; ring)
  have receipt (i : V) : ∑ T∈K.filter (fun T=>i∈T),cost T ≤ e := by
    let fitted:=K.filter (fun T=>i∈T)
    let all:=univ.filter (fun T : Finset V=>i∈T)
    have sub : fitted⊆all := fun _ ht=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ht).2⟩
    calc
      _ ≤ ∑ T∈fitted,e*∑ Z,tariff Z T*weight Z :=
        sum_le_sum fun T ht=>piece T (mem_filter.mp ht).1
      _ = e*∑ Z,(∑ T∈fitted,tariff Z T)*weight Z := by rw [← Finset.mul_sum,sum_comm]; simp only [sum_mul]
      _ ≤ e*∑ Z,(∑ T∈all,tariff Z T)*weight Z := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact sum_le_sum fun Z _=>mul_le_mul_of_nonneg_right
          (sum_le_sum_of_subset_of_nonneg sub (fun T _ _=>mul_nonneg (pow_nonneg hr _) (norm_nonneg _))) (Real.exp_pos _).le
      _ ≤ e := by
        have bill:=wallet i
        simp_rw [← root_sum] at bill
        exact (mul_le_mul_of_nonneg_left bill (Real.exp_pos _).le).trans_eq (mul_one _)
  calc
    ∑ T∈K,cost T ≤ ∑ T∈K,∑ i : V,if i∈T then cost T else 0 := by
      refine sum_le_sum fun T ht=>?_
      obtain ⟨i,hi⟩:T.Nonempty:=(mem_filter.mp (mem_filter.mp ht).1).2
      exact (if_pos hi : (if i∈T then cost T else 0)=cost T).symm.le.trans
        (single_le_sum (f:=fun j=>if j∈T then cost T else 0) (fun j _=>by split <;> first | exact norm_nonneg _ | rfl) (mem_univ i))
    _ = ∑ i : V,∑ T∈K.filter (fun T=>i∈T),cost T := by rw [sum_comm]; simp only [sum_filter]
    _ ≤ ∑ _i : V,e := sum_le_sum fun i _=>receipt i
    _ = _ := by simp [e]

/-- The actual normalized terminal polynomial pays for all cross-word factors.
The two physical moment conditions are supplied by calibrated_submoment. -/
theorem terminal_word {G : Gauge} (R : Rep G n) (X : Config G n → Π₀)
    (g : V → H) (o : V → Site n) (distinct : Injective o) (m L : ℕ)
    (fibres : ∀ j,(fibre g j).card ≤ m)
    (apart : ∀ i j,g i≠g j → 2*R.p.B+4*(2*R.p.B+1)*L<separation (o i) (o j))
    (pos : 0<L) {A D ρ a w s : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (radius : Real.exp (-A) ≤ ρ) (exponent : 1 ≤ a) (paid : m*A+D ≤ L)
    {b c : ℝ} (valid : R.activities.Valid R.p b c)
    (h : RGGapR2.Rough.Freight R (Stock.census V) X o (fun _=>ρ) a 1)
    (P : Π₀) (normalized : P=((X 1).part (Stock.census V).quiet)⁻¹ • X 1)
    (mom : ∀ T,‖P.part (tag T)‖ ≤ 1) (full : ∀ j,P.part (tag (fibre g j))=(w:ℂ))
    (hw : |w| ≤ 1) (hs : |s| ≤ 1/4) :
    ‖read g (s:ℂ) P‖ ≤ Real.exp ((Fintype.card V:ℝ)*Real.exp (-2*D))*(1+s*w)^Fintype.card H := by
  obtain ⟨C,silent,home,q,eq,bill⟩:=calibrated_terminal R (Stock.census V) X o (fun _=>ρ) a 1 valid h
    (fun _=>(Real.exp_pos _).le.trans radius)
  let logP:=∑ Z,C Z
  have silentLog : logP.part (Stock.census V).quiet=0 := by simp [logP,Poly.part_sum,silent]
  have quiet : P.part (tag ∅)=1 := by
    rw [normalized,eq]; exact Poly.pass_part logP silentLog
  let internal (T : Finset V):= ∃ j,T⊆fibre g j
  let I:=(occupied (V:=V)).filter internal
  let K:=external g
  let cost (T : Finset V):=logP.part (tag T)
  have tape : P=(∏ T∈I,(1+Poly.send (tag T) (cost T)))*(∏ T∈K,(1+Poly.send (tag T) (cost T))) := by
    rw [normalized,eq,TerminalGas.native_factors logP silentLog]
    exact (prod_filter_mul_prod_filter_not (occupied (V:=V)) internal _).symm
  have main:=factor_word_price g I K id cost
    (fun T ht=>⟨(mem_filter.mp (mem_filter.mp ht).1).2,(mem_filter.mp ht).2⟩)
    (fun T ht j inc=>(mem_filter.mp ht).2 ⟨j,inc⟩) P tape quiet mom full hw hs
  have fee:=cross_bill g o distinct m _ L fibres apart pos hA hD radius exponent paid C home bill
  have sw : |s*w| ≤ 1/4 := by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left hw (abs_nonneg s)).trans_eq (mul_one _)|>.trans hs
  exact main.trans (mul_le_mul_of_nonneg_right (Real.exp_monotone fee)
    (pow_nonneg (by linarith [neg_abs_le (s*w)]) _))

end YM.Integration.InletSusceptibility.Packet
