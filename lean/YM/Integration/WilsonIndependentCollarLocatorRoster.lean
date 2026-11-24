import YM.Integration.WilsonIndependentCollarLocatorPages
import YM.Integration.WilsonIndependentCollarSlateIntensity

/-! The square-free connected bank pays the sum over *all* genuine relative
fronts. Pulling its actual post-print rows back to the original charged
pages is injective, so the wallet is independent of the board volume. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarLocatorRoster
open Function Finset Lattice Laurent RG Wilson Precision Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity PhysicalNext.Repeat.Legato
open Push Push.AbsoluteSums Push.Local WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Address
open FundedMarkedPathSelection OriginalIssuedMarkedRows WilsonOlderFreshConnectedRobe WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedAppointment WilsonOlderFreshConnectedBirth WilsonOlderFreshGraphSlate
open WilsonRegisteredPairUnaryWallet WilsonOlderFreshGraphArmada
open scoped Classical BigOperators
variable {G:Gauge}{n e m N:ℕ}{D k:Fin n→ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
  (R:Run G)(V:Realm G (e+1) Credit.leanC)(hm:V.anchor ≤ m)(app:Paid R V hm D k δ σ)
  (c:Fin n)(X:Input V hm S k D A)(included:J⊆S)(live:c∈J)(apos:0≤A)
  (cut:m<N)(deep:0 < mass k J)(hs:0≤σ)(o:Cover)(v:Case D)
local notation "T" u:max => issued R V hm app N c X included live apos cut deep hs o v u
local notation "M" => R.family.path.levels.clock.hatBeta m^δ*A^J.card

def index:(Σ u:Frill J c,(T u).Roster)→Σ j:Fin (e+1),Page (G:=G) J c (mass k J) j.val:=
  fun z=>⟨z.2.1,z.2.2.1.1⟩

local notation "idx" => index R V hm app c X included live apos cut deep hs o v

theorem unique:Injective (idx):=by
  rintro ⟨u,j,⟨p,hp⟩,positive⟩ ⟨u',j',⟨p',hp'⟩,positive'⟩ h
  subst u u'
  change (⟨j,p⟩:Σ a:Fin (e+1),Page (G:=G) J c (mass k J) a.val)=⟨j',p'⟩ at h
  cases h
  rfl

theorem original {n':Side}(site:Frill J c→Site n'):
    SumBudget (fun z:(Σ u:Frill J c,(T u).Roster)=>
      Real.exp ((32*σ)*feeH (toe J c o z.1) c J)*
        (((T z.1).rows (WilsonOlderFreshGraphPointWallet.point (site z.1)) disk) z.2).height σ)
      (∑j:Fin (e+1),cost J (mass k J) j.val v (M)):=by
  let f:=fun z:(Σ j:Fin (e+1),Page (G:=G) J c (mass k J) j.val)=>
    Real.exp ((32*σ)*feeH (toe J c o z.2.2.1.1) c J)*
      ((roll V hm X J c (mass k J) N o v z.1.val).leg z.2).money (32*σ)
  have raw (j:Fin (e+1)):=WilsonIndependentCollarLocatorPages.original V hm X c (mass k J) N o v j.val
    (fun r=>(app N S J c A X included live apos cut).2 o j.val (by have hj:=j.isLt;omega) r)
  have whole:SumBudget f (∑j:Fin (e+1),cost J (mass k J) j.val v (M)):=by
    apply sumBudget_sigma (a:=fun j:Fin (e+1)=>cost J (mass k J) j.val v (M))
    · exact raw
    · exact ⟨fun j=>budget_nonneg (raw j),(hasSum_fintype _).summable,by rw [tsum_fintype]⟩
  apply sumBudget_mono (budget_pull (idx) (unique R V hm app c X included live apos cut deep hs o v) whole)
    (fun z=>mul_nonneg (Real.exp_pos _).le (mul_nonneg
      (((T z.1).rows (WilsonOlderFreshGraphPointWallet.point (site z.1)) disk) z.2).sound.le (Real.exp_pos _).le)) _ le_rfl
  intro z
  let b:=((T z.1).roll z.2.1).leg z.2.2.1
  have heard:=WilsonOlderFreshGraphMount.hearing (WilsonOlderFreshGraphPointWallet.point (site z.1)) b
    z.2.1 (mass k J) deep (((T z.1).paid z.2.1).pinned z.2.2.1)
    ((T z.1).legal z.2.1 z.2.2.1) z.2.2.2 σ (value disk) (b:=32*σ) (by linarith) hs
  have hinge:=z.2.2.1.2
  have row:(((T z.1).rows (WilsonOlderFreshGraphPointWallet.point (site z.1)) disk) z.2).height σ ≤
      Real.exp (σ*(WilsonOlderFreshGraphPointWallet.point (site z.1)).length)*b.money (32*σ):=heard
  have cable:(WilsonOlderFreshGraphPointWallet.point (site z.1)).length=0:=
    WilsonOriginalStarSceneRows.length _ _
  change _ ≤ Real.exp ((32*σ)*feeH (toe J c o z.2.2.1.1.2.1.1) c J)*b.money (32*σ)
  rw [hinge]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [cable,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul,Row.height] using row

end YM.Integration.WilsonIndependentCollarLocatorRoster
end
