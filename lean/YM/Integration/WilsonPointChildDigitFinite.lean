import YM.Integration.WilsonPointChildFiniteWard
import YM.Integration.WilsonPointChildDigitLedger
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildDigitFinite
open YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical
variable {G:Gauge}{d D:ℕ}
variable (R:Run G)(u:G.ColorIndex)(depth:d<D)
variable (digit:∀i,Site (R.family.S.block i))
variable (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

/-- Unaliased computation on the actual finite sides. At each date the
incoming quiet state is the true finite `story.1` on this same history. -/
def table (N:ℕ):ℕ→ℕ→Letter (R.family.labels.level d)→Scroll D→(n:Side)→PChart G n
  | 0, _, v, p, n => Shore.rancho
      (Kemp.banner d ((sectionY (R.family.localSection d) depth) v (physical p)) n)
  | h+1, j, v, p, n =>
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth digit N j
    Shore.rancho (∑s,Wine.worm (wire G n) ((T⁻¹) s v) *
      flash ((P.L.val^d) • WilsonMarkedFiniteIndependentStep.fixed R u tags N j n
       (skewV (wrap (n*P.L) (lift (digit j))) (table N h (j+1) s (growWord P (digit j) D p) (n*P.L)))))

open WilsonPointChildDigitLedger WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Winding
theorem original (simple:G.Simple)(o:Loc G 1)(price:ℕ→Gear G→ℝ)
    (paid:FundedMarkedCoverRows.prices price R.kit)(N h j:ℕ)(live:j+h≤N)
    (v:Letter (R.family.labels.level d))(p:Scroll D):
    ∀n,(ledger R u depth digit N h j v p).1 n=table R u depth digit tags N h j v p n:=by
  induction h generalizing j v p with
  | zero=>exact fun _=>rfl
  | succ h ih=>
    let V:=R.family.path.levels
    let P:=WilsonCoeffUV.loose V j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth digit N j
    let x:=growWord P (digit j) D p
    let upper(s:Letter (R.family.labels.level d)):=shifted (ledger R u depth digit N h (j+1) s x) (lift (digit j))
    let fired(s:Letter (R.family.labels.level d)):=verseI V R.metals.O j N d (upper s)
    let row(s:Letter (R.family.labels.level d)):Era G ℝ:=
      WilsonPointChildEra.funded ((T⁻¹) s v) ((P.L.val:ℝ)^d • fired s)
    have hz(s:Letter (R.family.labels.level d)):Auth d (upper s):=(honest R u depth digit simple o N h (j+1) (by omega) s x).shifted _
    have hs(s:Letter (R.family.labels.level d)):Auth d (fired s):=
      (hz s).verse V (by omega) simple R.alloy.B.ratio
    have paidrow(s:Letter (R.family.labels.level d)):Auth d (row s):=WilsonPointChildEra.checked ((hs s).μ _) _
    have eqn(s:Letter (R.family.labels.level d)):=ih (j+1) (by omega) s x
    intro n
    have all :=honest R u depth digit simple o N (h+1) j live v p
    have print:(ledger R u depth digit N (h+1) j v p).1 n=
          rancho (flash ((ledger R u depth digit N (h+1) j v p).1 n)):=by
        funext e r
        exact (WilsonConditionalTaylorWheelTensors.actual _ d (all.span n) (all.pale n) e r).symm
    rw [print]
    apply congrArg rancho
    change flash ((∑s,row s).1 n)=_
    rw [Prod.fst_sum,Finset.sum_apply,flash_term _ (fun s _=>(paidrow s).span n)]
    apply Finset.sum_congr rfl
    intro s _
    change flash (affix _ ((P.L.val:ℝ)^d • (fired s).1 n))=_
    rw [sponsor _ _ (mu_shellG ((hs s).span n) ((P.L.val:ℝ)^d))]
    change Wine.worm (wire G n) _ * flash ((P.L.val:ℝ)^d • (fired s).1 n)=_
    have fine:(upper s).1 (n*(Next.Free.destination V N j).patch.L)=_ := congrArg (skewV (wrap (n*P.L) (lift (digit j)))) (eqn s (n*P.L))
    rw [show (fired s).1 n=_ from WilsonMarkedFiniteIndependentStep.original R u tags simple price paid N j d (by omega) (upper s) (hz s) n,fine]
    rw [←Nat.cast_pow,Nat.cast_smul_eq_nsmul ℝ]
    rfl

end YM.Integration.WilsonPointChildDigitFinite
