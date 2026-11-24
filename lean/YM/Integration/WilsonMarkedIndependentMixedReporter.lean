import YM.Integration.WilsonMarkedIndependentMixedCompact
import YM.Integration.WilsonMarkedIndependentPhysicalIntake

/-! On the actual reporter, submit the localized full mixed source to the
native finite/cover marked comparison with an honest nonzero width. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedReporter
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open WilsonMarkedIndependentMixedStep (Entries)
open WilsonMarkedIndependentMixedGeometry (room)
open WilsonMarkedIndependentMixedCompact (clipped)
open WilsonMarkedIndependentPhysicalIntake (PairedAt)
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}[DecidableEq ι][Fintype ι]{D k:ι→ℕ}

def cost (G:Gauge)(k:ι→ℕ)(e:ℕ)(s C B:ℝ):ℝ:=1+B^(Fintype.card ι)+
  (∑r∈range (mass k univ+e+1), |priceM (Hooks G) r s+tiePay (Hooks G) r (s/4)+1|)*C^(Fintype.card ι)

omit [DecidableEq ι] in
theorem add_one (G:Gauge)(k:ι→ℕ)(e:ℕ)(s C B:ℝ)(c:0≤C)(b:0≤B):
    1≤cost G k e s C B:=by
  have z:0≤∑r∈range (mass k univ+e+1),|priceM (Hooks G) r s+tiePay (Hooks G) r (s/4)+1|:=
    sum_nonneg fun _ _=>abs_nonneg _
  unfold cost
  exact (le_add_of_nonneg_right (pow_nonneg b _)).trans (le_add_of_nonneg_right (mul_nonneg z (pow_nonneg c _)))

theorem paired (S:Schedule)(m p e M:ℕ)(Y:Outerm G D)(ρ s z C B:ℝ)(width:0<s)(pos:0<z)
    (c:1≤C)(b:1≤B)(well:Wellness k Y)
    (old:∀q I,shingled q I (reserveGood S m m ρ Y) e s C)
    (new:Entries Y S m m p e ρ B (Real.exp (-((S.side m p).val:ℝ)/(4096*z))))
    (stays:4*(M+12)<(S.side m p).val):
    PairedAt e (clipped M (reserveGood S m m ρ Y)) (S.side m p) (min (s/32) (1/(16384*z))) (cost G k e s C B):=by
  let Z:=clipped M (reserveGood S m m ρ Y)
  let n:=S.side m p
  let gross:=cost G k e s C B
  have g:1≤gross:=add_one G k e s C B (zero_le_one.trans c) (zero_le_one.trans b)
  have lawful:=WilsonMarkedIndependentMixedCompact.healthy M (reserveSpec S m m ρ well)
  intro q I i hi r
  by_cases blank:I=∅
  · subst I;rw [lawful.quiet' q];exact MarkU.zero.more (pow_nonneg (zero_le_one.trans g) _)
  have alive:=Finset.nonempty_iff_ne_empty.mpr blank
  have bright:0<I.card:=card_pos.mpr alive
  have count:I.card≤Fintype.card ι:=Finset.card_le_univ I
  by_cases kept:r ≤ mass k univ+e
  · by_cases short:crestCard q I≤M
    · by_cases safe:cleared S m m ρ q I
      · rw [clipped,if_pos short,reserveGood,if_pos safe]
        have space:room n q I:=by unfold room;dsimp only [n];omega
        have coverPrice:=old q I i hi r
        rw [reserveGood,if_pos safe] at coverPrice
        have actual:=WilsonMarkedIndependentMixedSpatial.restore alive width pos
          (pow_nonneg (zero_le_one.trans b) _) coverPrice (new I q alive safe space i hi r)
        apply actual.more
        apply le_trans _ (le_self_pow₀ g (Nat.ne_of_gt bright))
        let dx:=priceM (Hooks G) r s+tiePay (Hooks G) r (s/4)+1
        let total:=∑j∈range (mass k univ+e+1),|priceM (Hooks G) j s+tiePay (Hooks G) j (s/4)+1|
        have a:dx≤total:=(le_abs_self _).trans (single_le_sum (f:=fun j=>|priceM (Hooks G) j s+tiePay (Hooks G) j (s/4)+1|)
          (fun _ _=>abs_nonneg _) (mem_range.mpr (by omega)))
        have total0:0≤total:=sum_nonneg fun _ _=>abs_nonneg _
        have covered: dx*C^I.card ≤ total*C^Fintype.card ι:=mul_le_mul a
          (pow_le_pow_right₀ c count) (pow_nonneg (zero_le_one.trans c) _) total0
        have orig:B^I.card≤B^Fintype.card ι:=pow_le_pow_right₀ b count
        change dx*C^I.card+B^I.card≤1+B^Fintype.card ι+total*C^Fintype.card ι
        linarith
      · rw [clipped,if_pos short,reserveGood,if_neg safe];exact MarkU.zero.more (pow_nonneg (zero_le_one.trans g) _)
    · rw [clipped,if_neg short];exact MarkU.zero.more (pow_nonneg (zero_le_one.trans g) _)
  · have top:mass k I ≤ mass k univ:=Finset.sum_le_sum_of_subset (subset_univ I)
    have high:mass k I+i<r:=by omega
    rw [(lawful.level' q I).span _ _ _ high,(lawful.level' q I).coverN _ _ high]
    exact MarkU.zero.more (pow_nonneg (zero_le_one.trans g) _)

end YM.Integration.WilsonMarkedIndependentMixedReporter
end
