import YM.Integration.WilsonSeparatedOriginalProfileMarket
import YM.RG17.Profile
import YM.RG05Readout.Petals.Standing
import YM.XSpace.Carnation

/-! The charged physical estimate for every original separated test, including the issued Rose thermometer. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalProfileTest
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Pulse RG05Readout.Nuclear RG05Readout.Velvet
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open WilsonSeparatedOriginalProfileMarket
open scoped Classical BigOperators Topology ContDiff
universe u
variable {G:Gauge}(R:Run G)(simple:G.Simple){T:Campaign R}(W:Campaign.Pillars R T)
  {δ:ℝ}(fund:FundedOriginalProperties.{u} simple δ W)(book:OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
  (portfolio:Funding R)(slow:WilsonWindowReportingPace.Slow R.kit)
variable {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)
  {J:ℝ→FamilyBasis (C:=R.family) table}{u:Filter (ℕ×ℕ)}(B:Mantle F u)(E:OPE.Services R.family order table)
  (paid:Pier.Lair.Present F J)(pegs:Pegs B L)
  (near:∀ᶠr in trail,R.family.S.a (L.level r) ≤ r ∧ r ≤ R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)

def wave (φ:YM.Test 3):Wave (Fin 3):=⟨fun x:Cloud (Fin 3)=>φ (WithLp.toLp 2 x),φ.contDiff.comp PiLp.contDiff_toLp⟩

theorem qualified (φ:YM.Test 3)(rank:ℕ):
    ∃η X cap:ℝ,0<η ∧ η ≤ 1 ∧ 0 ≤ X ∧ 0 ≤ cap ∧ Scattering (wave φ) η ∧ Tall (wave φ) (rank+1) 1 X ∧
      ∀y∈tsupport (wave φ).val,∀i:Fin 3,‖y i‖ ≤ cap:=by
  let c:=PiLp.homeomorph 2 (fun _:Fin 3=>E4)
  have inside:tsupport (wave φ).val ⊆ (WithLp.toLp 2) ⁻¹' tsupport (φ:Points 3→ℂ):=
    closure_minimal (fun _ h=>subset_closure h) ((isClosed_tsupport _).preimage c.symm.continuous)
  have compact:HasCompactSupport (wave φ).val:=(φ.hasCompactSupport.image c.continuous).of_isClosed_subset
    (isClosed_tsupport _) (fun x hx=>⟨_,inside hx,rfl⟩)
  obtain ⟨cap,η,hc,hη,room⟩:=RG17.roomCosts φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨X,xp,bound⟩:=Petals.tall_any compact (rank+1)
  refine ⟨min η 1,X,cap,lt_min hη zero_lt_one,min_le_right ..,xp.le,hc,?_,bound,?_⟩
  · intro y hy i j different
    exact (min_le_left ..).trans (by simpa only [RG17.posed,one_smul,mul_one] using (room 1 one_pos _ (inside hy)).spaced i j different)
  · intro y hy i;simpa only [RG17.posed,one_smul,sub_zero,mul_one] using (room 1 one_pos _ (inside hy)).span i

def Charged (K d:ℕ)(s:Fin 3→ℕ)(v:(i:Fin 3)→Free R.family (s i))(φ:YM.Test 3):Prop:=
  ∃(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→R.family.label (s i))(k rank:ℕ)(η X cap:ℝ),
    (∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r)) ∧
    ∀γ:ℝ→ℝ,Coupling G γ → ∀p:ℕ,∀ε:ℝ,0<ε → ∀ᶠn:ℕ in atTop,∀ᶠr in trail,
      let m:=WilsonMeasuredWindow.stop R.family.path.levels simple K r;let H:=2*(h+1)+2*(K+1)
      ∃nm:n ≤ m,∀g:Body,∀l:Filter UVIndex,l ≤ L.lens → ∀ᶠz:UVIndex in l,
        Delivered R portfolio L s (w r) (wave φ) g nm rank d H k r η X cap (ε*γ r^p) z.1 z.2

include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:5 ≤ K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free R.family (s i))(φ:YM.Test 3):
    Charged R simple portfolio L (J:=J) K d s v φ:=by
  let rank:=(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)
  obtain ⟨η,X,cap,sp,small,xp,cp,scatter,height,shape⟩:=qualified φ rank
  obtain ⟨h,w,k,names,market⟩:=WilsonSeparatedOriginalProfileMarket.original R simple W fund book portfolio slow L B E paid pegs near K d hk s degree v
    (wave φ) rank sp small (Nat.lt_succ_self _) scatter xp height cp shape
  refine ⟨h,w,k,rank,η,X,cap,names,?_⟩;intro γ calibrated p ε ep
  filter_upwards [market] with n finance
  filter_upwards [finance,calibrated.positive] with r issue gp
  obtain ⟨nm,cost⟩:=issue
  exact ⟨nm,fun g=>cost g (ε*γ r^p) (mul_pos ep (pow_pos gp _))⟩

include W fund book slow B E paid pegs near in
theorem measured (K d:ℕ)(hk:5 ≤ K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free R.family (s i))
    {V:XSpace.Normalize.Store G}(rose:XSpace.Rose.Pick V):Charged R simple portfolio L (J:=J) K d s v (XSpace.Rose.test rose):=
  original R simple W fund book portfolio slow L B E paid pegs near K d hk s degree v (XSpace.Rose.test rose)

end YM.Integration.WilsonSeparatedOriginalProfileTest
