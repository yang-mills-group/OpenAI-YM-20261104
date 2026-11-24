import YM.Integration.WilsonLimitConstruction.FundedPresoldPacketWidths
import YM.Integration.WilsonThermometerUnitFilingLease
import YM.Integration.WilsonThermometerUnitFilingWeakStrip
import YM.Integration.WilsonOriginalCompoundVertexStrip

/-! Reserve the issued connected-packet width on the original compound teacher before block lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedBoard
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonOriginalCompoundStrip
open scoped Classical BigOperators
universe u
variable {G:Gauge}


open WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Cadenza Push.PriceCompiler
open FullQLocal FullQLocal.RenderedStep WilsonLimitConstruction QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor AllOrder AllOrder.Floe
abbrev Slots (H:ℕ):=Fin (H+1)×Fin (H+1)×Fin (H+1)

def whole : ProfileWidths where
  width _:=1
  positive _:=one_pos

def room (G:Gauge)(K:KernelChoices)(x H:ℕ)(t:Slots H):ℝ:=
  (FundedPresoldPacketWidths.profile G K t.1.val t.2.1.val t.2.2.val whole).width x

theorem positive (G:Gauge)(K:KernelChoices)(x H:ℕ)(t:Slots H):0<room G K x H t:=
  (FundedPresoldPacketWidths.profile G K t.1.val t.2.1.val t.2.2.val whole).positive x

def reserve (G:Gauge)(K:KernelChoices)(x H:ℕ):ℝ:=(1+∑t:Slots H,(room G K x H t)⁻¹)⁻¹

theorem one_slot (G:Gauge)(K:KernelChoices)(x H:ℕ):
    0<reserve G K x H ∧ ∀t,reserve G K x H ≤ room G K x H t:=by
  have pp(t:Slots H):0<(room G K x H t)⁻¹:=inv_pos.mpr (positive ..)
  have nn:0 ≤ ∑t:Slots H,(room G K x H t)⁻¹:=Finset.sum_nonneg (fun t _=>(pp t).le)
  refine ⟨inv_pos.mpr (by linarith),?_⟩
  intro t
  have hh: (room G K x H t)⁻¹ ≤ ∑s:Slots H,(room G K x H s)⁻¹:=
    Finset.single_le_sum (fun s _=>(pp s).le) (Finset.mem_univ t)
  unfold reserve
  exact (inv_anti₀ (pp t) (show (room G K x H t)⁻¹ ≤ 1+∑s:Slots H,(room G K x H s)⁻¹ by linarith)).trans (inv_inv _).le

def requested (Q:Request G):Request G where
  radius K x H:=min (Q.radius K x H) (reserve G K x H/32*(16*Q.multiplier H))
  positive K x H:=lt_min (Q.positive ..) (mul_pos (div_pos (one_slot ..).1 (by norm_num))
    (mul_pos (by norm_num) (Q.grows H)))
  multiplier:=Q.multiplier
  grows:=Q.grows
  entrance:=Q.entrance

def agenda (Q:Request G):Request G:=
  WilsonThermometerUnitFilingWeakStrip.enrolled (WilsonOriginalCompoundVertexStrip.narrowed (requested Q))

theorem retained (Q:Request G)(K:KernelChoices)(x H:ℕ):
    width (requested Q) K x H ≤ width Q K x H ∧ width (requested Q) K x H ≤ reserve G K x H/32:=by
  have h:0<16*Q.multiplier H:=mul_pos (by norm_num) (Q.grows H)
  exact ⟨min_le_min_left _ (div_le_div_of_nonneg_right (min_le_left ..) h.le),
    (min_le_right ..).trans ((div_le_iff₀ h).2 (min_le_right ..))⟩

theorem used (Q:Request G)(K:KernelChoices)(x H:ℕ):
    width (agenda Q) K x H ≤ reserve G K x H/32:=by
  let P:=WilsonOriginalCompoundVertexStrip.narrowed (requested Q)
  have h:width (WilsonThermometerUnitFilingWeakStrip.enrolled P) K x H ≤ width P K x H:=by
    apply min_le_min_left
    exact div_le_div₀ (P.positive ..).le (min_le_left ..) (mul_pos (by norm_num) (P.grows H))
      (mul_le_mul_of_nonneg_left (le_max_right 1 (P.multiplier H)) (by norm_num))
  exact h.trans ((WilsonOriginalCompoundVertexStrip.widths (requested Q) K x H).1.trans (retained Q K x H).2)

theorem anchored (Q:Request G)(R:Run G)(simple:G.Simple)
    (paid:WilsonThermometerUnitFilingCampus.Invoice (requested Q) simple (fun _=>MintClock.splits) R.kit)
    (ψ:ℕ → ℕ)(i H p k e l b:ℕ)(fit:H ≤ R.alloy.B.a.clock.J i)(work:1 ≤ k)(enough:H ≤ k+1)
    (born:p ≤ R.alloy.B.a.clock.J i+1)(grade:e ≤ H)(rank:l ≤ H)(arity:b ≤ H)
    (T:Realm G (e+1) Credit.leanC)(lo:T.anchor ≤ i)(five:5 ≤ R.family.path.levels.clock.J (i+1))
    (crest:(T.mint i lo).σ=crestM R.family.path.levels i five):
    let roots:=WilsonThermometerUnitFilingLease.roots (requested Q) simple (fun _=>MintClock.splits) R.metals.p R.metals.K
    let width:=Poetry.Agenda.seed roots ψ k (R.alloy.B.a.clock.J (i+1))
    0<width ∧ 32*width ≤ VestS b l T i lo:=by
  intro old σ
  have hi:=WilsonThermometerUnitFilingLease.original (requested Q) R simple paid ψ i H p k fit work enough born
  let P:=WilsonThermometerUnitFilingCampus.seated (requested Q) simple (fun _=>MintClock.splits) R.metals.p R.metals.K
  let V:=WilsonOriginalCompoundVertexStrip.narrowed P
  let K:=R.metals.p.kernel
  let x:=R.alloy.B.a.clock.J i
  have weak:width (WilsonThermometerUnitFilingWeakStrip.enrolled V) K x H ≤ width V K x H:=by
    apply min_le_min_left
    exact div_le_div₀ (V.positive ..).le (min_le_left ..) (mul_pos (by norm_num) (V.grows H))
      (mul_le_mul_of_nonneg_left (le_max_right 1 (V.multiplier H)) (by norm_num))
  have seat:width P K x H ≤ width (requested Q) K x H:=by
    apply min_le_min_left
    exact div_le_div_of_nonneg_right (min_le_left ..) (mul_pos (by norm_num) (Q.grows H)).le
  have cash:=hi.2.1.trans (weak.trans ((WilsonOriginalCompoundVertexStrip.widths P K x H).1.trans
    (seat.trans (retained Q K x H).2)))
  have h:= (one_slot G R.metals.p.kernel (R.family.path.levels.clock.J i) H).2
    (⟨e,by omega⟩,⟨l,by omega⟩,⟨b,by omega⟩)
  have hh:=FundedPresoldPacketWidths.live R l b whole i T lo five crest
  have kernel:R.family.path.levels.clock.kernel=R.metals.p.kernel:=R.alloy.B.valid.kernel
  rw [kernel] at hh
  change room G R.metals.p.kernel (R.family.path.levels.clock.J i) H
      (⟨e,by omega⟩,⟨l,by omega⟩,⟨b,by omega⟩) ≤ VestS b l T i lo at hh
  refine ⟨hi.1,?_⟩
  change σ ≤ reserve G R.metals.p.kernel (R.alloy.B.a.clock.J i) H/32 at cash
  have reach:=h.trans hh
  calc
    32*σ=σ*32:=mul_comm .. 
    _ ≤ reserve G R.metals.p.kernel (R.family.path.levels.clock.J i) H:=(le_div_iff₀ (by norm_num:0<(32:ℝ))).1 cash
    _ ≤ _:=reach

end YM.Integration.WilsonOlderFreshConnectedBoard
end
