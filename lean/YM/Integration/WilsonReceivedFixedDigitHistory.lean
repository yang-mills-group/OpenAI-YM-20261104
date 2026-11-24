import YM.Integration.WilsonMarkedIndependentOnePeriod
import YM.Integration.WilsonReceivedFixedDigitIntake

/-! Transport the actual winding inputs only along the successive sides of a single
period. Its width and cost precede both the top and the choice of period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedFixedDigitHistory
open Precision
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonFiniteMarkedHistoryStep
open scoped Classical BigOperators

variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ} {e : ℕ}

open WilsonMarkedIndependentPhysicalIntake (PositiveAt PairedAt narrow)

open WilsonMarkedIndependentOnePeriod (Course)

abbrev Digits (L:Levels G)(I:Type):=∀j:ℕ,I→Site (loose L j).L

def itinerary (L:Levels G)(O:ChartRatio G)(k:ι→ℕ)(N:ℕ)(c:Digits L ι):
    ℕ → ℕ → Outerm G D → Outerm G D
  | 0,_,Y=>Y
  | l+1,m,Y=>WilsonReceivedFixedDigitIntake.next L O m N k (itinerary L O k N c l (m+1) Y) (c m)

omit [Fintype ι] in
theorem sound (L:Levels G)(O:ChartRatio G)(k:ι→ℕ)(N:ℕ)(c:Digits L ι)
    (simple:G.Simple)(ratio:LocalRatio O)(Y:Outerm G D)(well:Wellness k Y)(days m:ℕ)(cut:m+days≤N):
    Wellness k (itinerary L O k N c days m Y):=by
  induction days generalizing m with
  | zero=>exact well
  | succ d ih=>
    exact WilsonReceivedFixedDigitIntake.lawful L O m N k _ _ simple ratio (by omega) (ih (m+1) (by omega))

private theorem descend (Q : Realm G (e+1) Credit.leanC) (days : ℕ) :
    ∀ m b : ℕ, Q.anchor ≤ m → b = m+days → ∀ {s : ℝ}, 0 < s →
    ∃ (d : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, b ≤ N →
    ∀ (Zs : Course Q.draws) (cells:Digits Q.draws ι) (Y : Outerm G D), Wellness k Y → ∀ V A : ℝ, 1 ≤ V → 1 ≤ A →
      PositiveAt Q.draws Q.paid e N b (Zs.side b) s V →
      PairedAt e Y (Zs.side b) s A →
      PositiveAt Q.draws Q.paid e N m (Zs.side m) σ (C*V^d) ∧
      PairedAt e (itinerary Q.draws Q.paid k N cells days m Y) (Zs.side m) σ (C*V^d*A) := by
  induction days with
  | zero =>
    intro m b _ date s hs
    have same : b=m := by omega
    clear date
    subst b
    refine ⟨1,1,s,le_rfl,hs,?_⟩
    intro N top Zs cells Y well V A hV hA quiet old
    simp only [itinerary,pow_one,one_mul]
    exact ⟨quiet,narrow old le_rfl (zero_le_one.trans hA)
      (le_mul_of_one_le_left (zero_le_one.trans hA) hV)⟩
  | succ days ih =>
    intro m b hm date s hs
    have mb : m+1 ≤ b := by omega
    obtain ⟨u,C,t,hC,ht,deposited⟩ := ih (m+1) b (hm.trans (Nat.le_succ _)) (by omega) hs
    obtain ⟨r,W,w,hW,hw,quietStep⟩ := WilsonMarkedIndependentPhysicalQuiet.posted Q hm ht
    obtain ⟨h,B,v,hB,hv,markedStep⟩ := WilsonReceivedFixedDigitIntake.posted (D:=D) (k:=k) Q hm ht
    let p := max r (h+1)
    let H := max W B * C^p
    have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le (hW.trans (le_max_left ..)) (one_le_pow₀ hC)
    refine ⟨u*p,H,min w v,hH,lt_min hw hv,?_⟩
    intro N top Zs cells Y well V A hV hA quiet old
    let Z := itinerary Q.draws Q.paid k N cells days (m+1) Y
    let T := C*V^u
    have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hV)
    have hTA := one_le_mul_of_one_le_of_one_le hT hA
    have live : m < N := mb.trans top
    obtain ⟨previous,faces⟩ := deposited N top Zs cells Y well V A hV hA quiet old
    have laws : Wellness k Z := sound Q.draws Q.paid k N cells Q.hG Q.green Y well days (m+1) (by omega)
    rw [Zs.next m] at previous faces
    have quietOut := quietStep N live (Zs.side m) T hT previous
    have markedOut := markedStep N live (Zs.side m) Z laws T (T*A) hT hTA previous faces (cells m)
    have equal : max W B * T^p = H * V^(u*p) := by
      dsimp [H,T]; rw [mul_pow,pow_mul]; ring
    have cw : W*T^r ≤ H*V^(u*p) := by
      rw [←equal]
      exact mul_le_mul (le_max_left ..) (pow_le_pow_right₀ hT (le_max_left ..))
        (pow_nonneg (zero_le_one.trans hT) _) (zero_le_one.trans (hW.trans (le_max_left ..)))
    have cm : B*T^h*(T*A) ≤ H*V^(u*p)*A := by
      rw [←equal,show B*T^h*(T*A) = B*T^(h+1)*A by rw [pow_succ]; ring]
      apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hA)
      exact mul_le_mul (le_max_right ..) (pow_le_pow_right₀ hT (le_max_right ..))
        (pow_nonneg (zero_le_one.trans hT) _) (zero_le_one.trans (hB.trans (le_max_right ..)))
    refine ⟨fun a _ ha l _ => ((quietOut a ha (l+1)).mono (min_le_left ..)).more cw,?_⟩
    change PairedAt e (WilsonReceivedFixedDigitIntake.next Q.draws Q.paid m N k Z (cells m)) _ _ _
    exact narrow markedOut (min_le_right ..) (by positivity) cm

/-- The marked row traverses all genuine dates from b down to m. The upper
bound for the initial quiet tensor is the only remaining ultraviolet input. -/
theorem original (Q : Realm G (e+1) Credit.leanC) (m b : ℕ)
    (hm : Q.anchor ≤ m) (mb : m ≤ b) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 1 ≤ C ∧ 0 < σ ∧ ∀ N, b ≤ N →
    ∀ (Zs : Course Q.draws) (cells:Digits Q.draws ι) (Y : Outerm G D), Wellness k Y → ∀ V A : ℝ, 1 ≤ V → 1 ≤ A →
      PositiveAt Q.draws Q.paid e N b (Zs.side b) s V →
      PairedAt e Y (Zs.side b) s A →
      PositiveAt Q.draws Q.paid e N m (Zs.side m) σ (C*V^d) ∧
      PairedAt e (itinerary Q.draws Q.paid k N cells (b-m) m Y) (Zs.side m) σ (C*V^d*A) :=
  descend Q (b-m) m b hm (by omega) hs

end YM.Integration.WilsonReceivedFixedDigitHistory
end
