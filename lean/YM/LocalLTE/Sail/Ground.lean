import YM.LocalLTE.Sail.Chronicle
import YM.LocalLTE.XPre.Kudos
import YM.LocalLTE.XPre.Trump
import YM.LocalLTE.XPre.Dispatch
import YM.LocalLTE.XPre.Flotilla
import YM.LocalLTE.Ticket.Tissue
/-! Reworking `XPre/Hill` for schedules with explicit, controlled guide functions.


# Canonical synthesized *actual* appointments and calibration at H
Meet with Lamp circuit.Packs.Alerts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Bandage Mallow
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.XPre
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
section
open Push.Local LocalLTE.Dilation Extra.Histories.Doors
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
local notation "H"=> Issue.trail P
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ} (U:Harmonics R C W P l)
-- window opportunities using after-L supports. 
variable {N n m:ℕ} (hm:m<N)
local notation "T"=> U.port N m n hm
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "Y"=> A.B.a.clock.hatBeta m
set_option quotPrecheck false
open Pressure ConnectedActivityE6 Push.AbsoluteSums
variable (hG:G.Simple)
-- recall after.App durations
open Spiral
variable {M p0 r q TT :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hp:East.stagnate q 500<l)(hR:∀ i j,(R.target i j).halo=500)
include hr
variable (d j:ℕ)(hd:d+3 ≤ A.B.a.clock.J m)
local notation "a"=> AX.demand J I j
local notation "f"=> AX.outfit J I j
local notation "u"=> AX.atlas J I j
local notation "R1"=> (H).rep N n (m+1)
local notation "S₀"=> (H).rep N n m
local notation "B"=> A.B.a.budget m
local notation "B'"=> (localSection G d)
local notation "F0"=> ((Labels.frames G).level d)
local notation "V'"=> Bandage.aperture U.tag N m n T d hd
local notation "L"=> D.L J
local notation "K₀"=> U.space N m n hm
local notation "Zs"=> (R.shape.μ J I)
local notation "X'"=> X.p.profile I
local notation "Z'"=> X.p.profile J
local notation "κz"=> (T).ranch.allocation.κ
local notation "B0"=> 2* Legato.ticR G (X.p.profile J)
local notation "gn"=> Local.factor (hol G) B' (B).supportExponent (Cub.title G (X.p.profile I))
-- prices minted after Pt.E. Use post-block polynomial.
omit hr
open LocalLTE.XPre
local notation "VZ"=> U.kube N (m+1) n hm
local notation "e0"=> U.lays d N n m hm
local notation "κg"=> Push.Local.factor (hol G) (localSection G d) ((X.p.profile I).supportExponent) (Cub.title G (X.p.profile I))
local notation "AΓ"=> (sill (X.p.profile I).supportExponent l)
local notation "GS"=> (X.p.profile I).supportExponent
-- generic calendar acquiring these prices to cap.Source.Weight.
include hr
include hd hκ hG
open Lotus
lemma preQC : ∃ Xr:Set Lotus.Wing, Xr.Finite ∧ (∀ i, (Lotus.Wing.gasKey (cart (R:=R1) (VZ) i))∈ Xr)∧ LocalLTE.XPre.Permits (R1) (S₀) Xr (U.deed N n m hm) d (((((Issue.trail P).S.block m).val:ℂ)^d)) e0 (payG G X' Z' l d L) κ a (((D.L J).val) *radiusB Y):=by  -- HX
    let K0:= (K₀); let M':=(T); let b:= U.tag; have ht := step_paid A.B.a m; have hy:= (Nat.le_add_right d 3).trans hd
    have hz := U.ore (n:=n) hm; let G0:= Cub.lightPlant M' (V') hz l K0; have he := U.baptism N m n hm; have hx := U.charged N m n hm
    let n':= (H).S.side (m+1) n; let a0 (i:{i:Support n'//0∈i}):Wing:= .logKey (Blush.found 0 i.val i.property); let k(i:StockTag n'):Wing:=.gasKey (cart (VZ) i); let s:= Set.range a0∪ Set.range k
    refine ⟨s,(Set.finite_range a0).union (Set.finite_range k),fun i=>Or.inr ⟨i,rfl⟩,?_⟩
    have hL: (H).S.block m=(D.L J):= Push.PriceCompiler.block_eq A.B.valid m
    unfold Harmonics.lays Bandage.purser; rw [dif_pos hd,hL]; apply Harmonics.retreat
    obtain ⟨hw,hβ,hT,-⟩:= (hr.provision.limits _ _ ht _ (A.B.valid.pays m)).2 d hy
    have htG:minSide G d ≤ M'.inPort.p.B:=by rw [M'.senses.1.point]; change _≤ radiusB (A.B.a.clock.hatBeta (m+1)); rw [beta_eq A.B.valid]; exact hβ
    let g:= payG G X' Z' l d L; let Λ:= (((D.L J).val:ℂ)^d); let h':=a; let Kx:=κz
    have hE : (B).supportExponent=(X.p.profile I).supportExponent:= Rain.jersey (A:=A) (m:=m)|>.2.2.1
    apply Eq.mp (congr_arg (fun τ:ℝ=> LocalLTE.XPre.Permits M'.inPort M'.output s M'.door d Λ G0 g τ (h') (((D.L J).val) *radiusB Y)) ((hκ _ _ _ hm).2))
    change XPre.Permits M'.inPort M'.output s M'.door d Λ G0 g κz (a) _
    refine ⟨fun i hi=> ?_,fun f' g' V dx dv du hF hc hq hQ he' => ?_,fun f' j x y hh hJ hF hf hh' =>?_⟩
    · obtain ⟨v,hV⟩:= Cub.wagesB hm b.songs b.PStage b.wait (Graces.feet hd b.clock) (U.samples N m n hm.le) b.r M' he hx hG b.tunes b.shape b.clock b.stamp hd hz V' i hi
      have ho:=Turf.untether M' hm l h' d hG b.r K0 (V') hz i hi ((hT _).2) hV P he b.clock b.stamp hd htG s (show (Lotus.Wing.logKey (Circlet.badge G ((Issue.trail P).S.side (m+1) n) d))∈ s from Or.inl ⟨⟨_,Circlet.ankle⟩,rfl⟩) -- order
      rw [hE] at ho
      let e:= Legato.cl0 (X.p.profile J) d L; rw [show AΓ*e + κg*(AΓ*e)= g.grant from ?_] at ho
      · exact ho
      dsimp only [g,payG]; ring -- edit
    ·
      have hp: (.logKey (Blush.found 0 V hF.anchor))∈ s:= Or.inl ⟨⟨V,hF.anchor⟩,rfl⟩
      let X0:Turf.Holds M' d V f' dx:=⟨hF,hq⟩; let Xv:Turf.Holds M' d V g' dv:=⟨hc,hQ.value⟩
      have h0:= Turf.solos M' hm l h' d hG b.r K0 (α:=dv) (z0:=dx) hz Xv hQ P (U.samples N m n hm.le) hx he b.tunes b.furthering b.clock b.stamp hd X0 he' s hp -- order
      rw [hE] at h0; let uT:= M'.inPort.p.mass V dx
      rw [show AΓ*(Doors.rate L*uT)+κg*(AΓ*(Doors.rate L*uT))=g.canopy*uT from ?_] at h0
      · exact h0
      dsimp only [g,payG]; ring
    let yT:=M'.inPort.p.mass (M'.inPort.activities.forced j).support y
    have hp := Turf.TabletV.dark M' hm l h' d hG b.r K0 f' j hF hh P (U.samples N m n hm.le) hx he b.clock b.stamp hd x y hf hh' s hJ -- order likely
    rw [hE] at hp; rw [show AΓ*(Doors.rate L*yT)+κg*(AΓ*(Doors.rate L*yT))=g.canopy*yT from ?_] at hp
    · exact hp
    dsimp only [g,payG];ring
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
