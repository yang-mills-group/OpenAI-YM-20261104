import YM.Integration.WilsonMatrixTicketFuelPrice
import YM.OPE.Retained.Niche.Derma

/-! Near-null estimates on the realized retained history and its true fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
open OPE.Owl.Retained OPE.Votive.Retained

open OPE OPE.Owl
set_option quotPrecheck false
variable {g:G.Simple}{s: Sheet G}{p:MapPrices}{H:Votive.Sponsor G}{K:Votive.Seasons H}{a:Axis}{X:Stroke.PriceBook (chart_ok G) K}{t:ℕ→ℕ} {U:Rolls (ThroughLaunch.raise s t)}{P:Spells.Pad G}{D:Desk (ThroughLaunch.raise s t) X a g} {S: Alloy (ThroughLaunch.bountyV s p t) U}
namespace FuelV
variable (C:FuelV g s p H K a X t U P D S)
open OPE.Lake OPE.Allot
variable {l m p' i:ℕ}
variable (u:Ultrafilter (ℕ×ℕ)){F : Extraction.Order}(h:(u:Filter _)≤ F.fuse)
local notation "vν"=> S.B.a.clock.J

local notation "P!"=>constellation D l
open Eyrie Extraction -- open for Bid.


local notation "Q"=> C.Holds
-- one-filtration opacity. Uniform in fixed entries up to 2. tolerance can be tiny in p, ascent of support bought along levels.
structure Opacity (C:FuelV g s p H K a X t U P D S) (ε:ℝ) :Prop where
       price : 0<ε
       toll : ε≤1/50
       charge :∀ l r:ℕ,∀ᶠ m:ℕ in atTop,∀ (hp:C.refQ l ≤ m)(he:D.cost l ≤ S.B.a.clock.J m),∃ v:ℕ→ℝ,(∀ i,0<v i) ∧ ∀ᶠ i:ℕ in atTop,∀ N,∀ ht:m+1<N,∀ (R:C.PlaneQ l m N i hp (Nat.lt_trans (Nat.lt_succ_self m) ht)),PassportQ C hp (Nat.lt_trans (Nat.lt_succ_self m) ht) he R→∀ x:C.Holds.label l, ‖x‖ ≤ 2→Pennant (C.Holds.path.rep N i m) (fleet C.Holds.path m r) (v i) ((Owl.Stepm C.makes (d:=l) hp ((Nat.lt_trans (Nat.lt_succ_self m) ht).le) i x).density 0 (C.Holds.localSection l) (C.Holds.path.rep N i m)) → ‖Tplane C hp (Nat.lt_trans (Nat.lt_succ_self m) ht) he R x‖≤ CardinalQ.ages (-1-ε) (S.B.a.clock.hatBeta m)
end FuelV
open CardinalQ
variable {g:G.Simple}{s: Sheet G}{p:MapPrices}{H:Votive.Sponsor G}{K:Votive.Seasons H}{a:Axis}{X:Stroke.PriceBook (chart_ok G) K}{t:ℕ→ℕ} {U:Rolls (ThroughLaunch.raise s t)}{P:Spells.Pad G}{D:Desk (ThroughLaunch.raise s t) X a g} {S: Alloy (ThroughLaunch.bountyV s p t) U}
variable (C:FuelV g s p H K a X t U P D S)
variable {l m N k r:ℕ}{u ε:ℝ}(he:D.cost l ≤S.B.a.clock.J m)(hk:C.refQ l ≤ m)
local notation "i₀"=> S.B.a.clock.J m
local notation "Y!"=> D.stream l
local notation "σ"=> S.θ.theta i₀
local notation "v"=> S.B.a.clock.hatBeta m
local notation "F"=> s.profile i₀
local notation "W₀"=> D.OAuth l i₀ he
lemma FuelV.unbound (i:ℕ)(hk:i<N)(y:C.Holds.label l)(hv:C.Holds.ref l ≤ i) : Continuous ((Stepm C.makes hv hk.le k y).density 0 (C.Holds.localSection l) (C.Holds.path.rep N k i)) :=by
        let A:= C.Holds; let T:= A.path; let K:= C.makes; let x:= Lot (m:=i) K hv hk.le k y; let L:= A.factory l N k
        change Continuous ((L.entries i x).density 0 _ _); have hh:= K.calibrated l N k (hv.trans hk.le); have hz:=(hv.trans (Nat.le_succ i)); let a:=L.entries (i+1) x; let f:= a.density 0 (A.localSection l) (T.rep N k (i+1)); let Q:= T.levels.clock.op i k
        have he:Continuous (Q.push (T.β N k (i+1)) f):= by
             let c:= (T.rep N k (i+1)).beta
             exact Push.Local.Kernel.pass_continuous Q c Finset.univ (T.levels.blocks i k).branches (play_integrable T N K.wilson hk (hh.format _ hz hk x) (hh.cap _ hz hk x))
        have equality := hh.unnormalized i hv hk x
        exact (congrArg Continuous equality).mpr (he.const_smul _)
include C
lemma FuelV.ExLease (h:Freeze g P (Y!) he F W₀ σ ε v (Eyrie.rim i₀ r)) :∃ V:ℕ→ℝ,(∀ i,0<V i) ∧ ∀ᶠ i:ℕ in atTop,∀ N,∀ ht:m+1<N,∀ (R:C.PlaneQ l m N i hk (Nat.lt_trans (Nat.lt_succ_self m) ht)),FuelV.PassportQ C hk (Nat.lt_trans (Nat.lt_succ_self m) ht) he R→∀ x:C.Holds.label l, ‖x‖ ≤ 2→Eyrie.Pennant (C.Holds.path.rep N i m) (Eyrie.fleet C.Holds.path m r) (V i) ((Owl.Stepm C.makes (d:=l) hk ((Nat.lt_trans (Nat.lt_succ_self m) ht).le) i x).density 0 (C.Holds.localSection l) (C.Holds.path.rep N i m))→ ‖FuelV.Tplane C hk (Nat.lt_trans (Nat.lt_succ_self m) ht) he R x‖ ≤ CardinalQ.ages (-1-ε) (S.B.a.clock.hatBeta m) :=by
        obtain ⟨n,hθ⟩:= h.buy.exists; let X(i:ℕ):=S.B.a.S.side m i; let W:= hθ; have ht := Stationary.bound_climb G S.B.a m|>.eventually_ge_atTop n
        choose! z hz he' using fun i (h:n ≤ (X i).val)=> hθ (X i) h
        let V i:= if n ≤ (X i).val then z i else 1
        refine ⟨V,(fun i=>by unfold V; split_ifs with h; exact hz i h; norm_num),?_⟩
        filter_upwards [ht] with i hT N hn R hR x h_x hv
        have hN:= Nat.lt_trans (Nat.lt_succ_self _) hn; let Q:= OPE.Owl.Retained.Capton (A:=S) C.turtle C.tell hN; let L:= C.Holds.path.rep N i m
        have hp: (C.Holds.path.levels.params m)=F:=params_eq S.B.valid m
        have hx: (C.Holds.path.levels.clock.loopCap m)= CardinalQ.capL σ v:= OPE.Owl.Retained.SoftRise C.turtle C.tell hN
        rw [show V i=z i from if_pos hT] at hv; have hy := (C.makes.wilson.represents N i m hN.le).good
        change L.Lawful (C.Holds.path.levels.params m).width (C.Holds.path.levels.params m).paths
          (C.Holds.path.levels.clock.loopCap m) _ _ at hy
        rw[hp,hx] at hy; exact he' i hT L _ R Q (OPE.Owl.Retained.linK C.amp C.turtle C.tell hN) hR.face (OPE.Owl.Retained.SoftRise C.turtle C.tell hN) hy x h_x (C.unbound m hN x hk) hv

theorem FuelV.purchased (hε:0<ε) (hcap:ε≤1/50)
    (price:Integration.WilsonMatrixTicketFuelPrice.Frozen D P ε S.θ S.delay) : C.Opacity ε := by
  refine ⟨hε,hcap,fun l r=>?_⟩
  filter_upwards [S.B.a.fits.deep.eventually_ge_atTop r] with m hr hp he
  exact C.ExLease he hp (price (S.B.a.clock.J m) _ r l he hr
    (S.B.a.fits.mono (Nat.le_succ m)) _ (S.B.valid.pays m))
end YM.PhysicalNext.Repeat.Legato

namespace YM.Integration.WilsonMatrixTicketFuelPrice
open PhysicalNext.Repeat.Legato
open Lattice

theorem issued {G:Gauge} (R:Run G) {g:G.Simple} {a:Axis} {ε:ℝ} (hε:0<ε) (hcap:ε≤1/50)
    (funded:Eligible g a ε R.kit) : ∃ L:Licence g a ε R.kit R.family, L.physical.Opacity ε := by
  obtain ⟨L⟩:=on_run funded
  exact ⟨L,L.physical.purchased hε hcap L.frozen⟩
end YM.Integration.WilsonMatrixTicketFuelPrice
