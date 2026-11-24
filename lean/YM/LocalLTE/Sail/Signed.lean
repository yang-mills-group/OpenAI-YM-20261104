import YM.LocalLTE.Sail.Square
/-! Precise local public contract. Producer downstream for any basis.Epoch.Program. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow LocalLTE.Sail Spiral
variable {G:Gauge} {X: Metals G} {D: Rolls X.p} {A:Alloy X D}{P:Bolt A}{C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}{R:Factor A}
local notation "H"=> Issue.trail P
open Bandage
variable (U:Bandage.Harmonics R C W P l)
variable {M p0 r q TT K P0 p' :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)(hp: Market M K P0 p0 TT l G ζ A.delay) (hD: Patronage K P0 p' p0 TT ζ A.delay)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hG:G.Simple)(hL:∀ i j,(R.target i j).halo=500)(hl:East.stagnate q 500<l) (he:0<ζ)
variable {z:GuideF} {Tt:ℕ→ Mallow.ConcertZ R.target M ζ}(hU: Mobility AX R.shape A.delay z Tt K l TT κ)
variable (r0:ℕ→ℕ)(hV:∀ d,d+3 ≤ (Issue.trail P).levels.clock.J (r0 d))
variable (T: ∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail P) N p)
variable (hC: (Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) r0 T).Makes)
-- LIVE proof with label.transform accessibility on all stages. Interpreted probes version. Across choices of blocks expression may change.CAL.Phys exactly SAME.
include U hr hκ hU hl hL
structure Survey (P0 p':ℕ):Prop where
    controls : ∃ (V:∀ N p d,Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N p),
        (∀ d N p, r0 d≤N → (T d N p).entries=((V N p d).draft (Issue.trail P)).inits ∧ U.Registers (V N p) d (r0 d)) ∧
        ∀ (I:Type)[DecidableEq I][Fintype I](B:Marker.Census I)(N n m:ℕ), m<N→ N-m≤TT+1 → ∀ (Y:Batch (Issue.trail P) N n I) (v₀:I), Y.Wants m r0 K →
           (∀ i:I,Y.wavelengths i=((A.B.a.S.a N:ℂ)^(Y.demand i)) • YM.MergeProof.stepUp (Y.motion i) (Y.origin N i) ((Family.mk H (hol G) (Labels.frames G) (localSection G) r0 T).O N n ((T (Y.demand i) N n).terminal (Y.voice i)) 0)) ∧ Nonempty (∀ i:ℕ,i≤N→ Y.steering i) ∧
            ∀ (π:∀ i:ℕ,i≤N→Y.steering i)(Yg:(i:ℕ)→ LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side i n))), ∃ F O, U.Polar (V N n) hr hκ hL hl B Y v₀ hU π Yg F O m P0 p'
-- user craft.Any.
include hp hD hC hG he hV
lemma survey_present (h:∀ d N n,r0 d≤N → Bandage.Stately U d N n (T d N n) (r0 d)) : Survey U hr hκ hL hl hU r0 T P0 p' :=by
   choose V hV' using fun N n=> U.premise r0 T N n (fun d=> h d N n)
   refine ⟨V,fun d N p=> hV' N p d,fun Z _ _ B N n m hx h' Y v₀ hk=>?_⟩
   have hp0:∀ i:ℕ,i ≤ N→ Nonempty (Y.steering i):=by
       intro i hi
       exact Classical.nonempty_pi.mpr fun v=> (P.choice.represents N n i hi).good.labels.moves (Y.motion v).1 (Y.origin i v)
   refine ⟨fun i=> Bandage.Harmonics.birth_operators r0 Y T i, ⟨fun i hi=> (hp0 i hi).some⟩,?_⟩ -- arity
   intro π Yg; exact U.embassy (V N n) r0 hV hr hp hD hκ hG hL hl he B Y v₀ ⟨hk,fun i=> (hV' N n _ ((hk.registered i).trans hx.le)).2.contract⟩ (fun d hd=> (hV' N n d hd).2) hU π Yg T hC hx h'
end YM.PhysicalNext.Repeat.Legato
