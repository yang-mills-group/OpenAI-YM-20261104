import YM.GapsR2RG.FiberRegular
import YM.GapsR2RG.FiberK
/-! # Producer at ANY fine address in parent center: same Fields & Tune as RG17 Run
 Extracted nucleus of Crowding/Basal calculation; retain exact Gig including
 Forced entries and enough width+order for the actual response. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.GapsR2RG.Anchor
open Lattice Wilson RG RG.Activities PhysicalNext Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Legato.Bandage Graces JointLoad.Heir Next.Foundations
open Labels Source Function Filter Set MeasureTheory Finset Extra.Histories Extra.Histories.Relay MergeProof
open Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open scoped Classical Topology Matrix.Norms.Frobenius ContDiff BigOperators
set_option quotPrecheck false
variable {G:Gauge}(h:G.Simple)(R:Run G){N p m d:ℕ}(hm:m<N)(hd:R.t d ≤ m)
local notation "c₀" => (R.family.side (m+1) p)
local notation "c'" => R.family.side m p
local notation "H'" => R.family.path
local notation "R'" => (H').rep N p (m+1)
local notation "D'" => (H').levels.clock.op m p
include h hm hd R
set_option maxRecDepth 30000
lemma fibers (ι : Site (R.family.side (m+1) p))(hι : (D').ratio.parent ι=0) : let e := Doors.rate ((H').S.block m)
     (∀ (c:Config G (c₀) → ℂ) X a, RegFit R' ι d (hol G) X c → (R').p.supBounds ι X c a → let t:=e*(R').p.mass X a
        ∃ P,Gig (localSection G d) H' N p m (hol G) (salary R' X c) P 0 t t) ∧
     (∀ (c:Config G (c₀) → ℂ) (j:ℕ) a, SlotFit R' ι j c → 0 ≤ a → (∀ V,‖c V‖ ≤ a) → let y:=(R').p.mass ((R').activities.forced j).support a; let t:=e*(y/Real.sqrt ((H').levels.clock.forcedAllowance (m+1)))
        ∃ P,Gig (localSection G d) H' N p m (hol G) (fare R' j c) P 0 t t) :=by
   intro e
   obtain ⟨l,v,Q,U,x,hE,hP,hx⟩:= R.carries N m p hm
   have hW:= R.tuning.receipts
   let A:=R.alloy
   have hM:= (R.accepts d).trans ((Issue.trail R.T).levels.fits.mono hd)
   let L:=R.rolls.L (A.B.a.clock.J (m+1))
   have hr:(H').S.block m=L:= Push.PriceCompiler.block_eq A.B.valid m
   unfold e; have hP':R'=Q x:=hP; rw [hr,hP']; constructor
   · intro f Xp a hf ha t
     obtain ⟨Q,hQ,_⟩:=grow (regularFiber h hm hW R.b.r R.b.tunes R.b.furthering hM R.b.clock R.b.stamp U x hP hE (hP ▸ hW.samples h N (m+1) p hm) ι hι Xp a f hf ha) (R.makes.wilson.represents N p m hm.le) ((R.makes.wilson.represents N p m hm.le).vac.symm ▸ livelyCard R.b.clock (le_trans (by omega) hM))
     exact ⟨Q,hQ⟩
   intro c j a hS hA ht k t
   by_cases hu:c=0
   · have hF : 0 ≤ t:= by have hv:= Doors.rate_pos L; change 0 ≤ Doors.rate L * (k/Real.sqrt _); have hv':0 ≤ k:=  mul_nonneg (Real.exp_pos _).le hA; positivity -- maybe k defeq Mass unfolds
     obtain ⟨P,hv,_⟩:= (zeroSlot (localSection G d) H' N p m (hol G) Set.univ (R.doors N p m hm) R.makes.wilson hF hF)
     exact ⟨P,(show Extra.Histories.fare _ j c=0 from funext fun V=> by unfold Extra.Histories.fare; rw [hu]; dsimp only [Pi.zero_apply]; ring).symm ▸ hv⟩
   exact heavyFiber h hm hW R.b.r U x hE hP R.b.clock R.b.stamp (le_trans (by omega) hM) ι hι (R.makes.wilson.represents N p m hm.le) j c a hu hS ht
end YM.GapsR2RG.Anchor
