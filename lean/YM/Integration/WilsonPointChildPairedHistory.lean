import YM.Integration.WilsonPointChildFoldedField
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildPairedHistory
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{d D:ℕ}
variable (R:Run G)(u:G.ColorIndex)(depth:d<D)
variable (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

/-- The two entries of this ledger use the genuinely same marked operation
and its unchanged pupil, on the finite torus and the cover. -/
def ledger (N:ℕ):ℕ→ℕ→Letter (R.family.labels.level d)→Scroll D→Era G ℝ
  | 0, _, v, p => WilsonPointChildFoldedField.field d
      ((sectionY (R.family.localSection d) depth) v) (physical p)
  | h+1, j, v, p =>
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth (fun _=>0) N j
    ∑s,WilsonPointChildEra.funded ((T⁻¹) s v)
      ((P.L.val:ℝ)^d • verseI R.family.path.levels R.metals.O j N d
        (ledger N h (j+1) s (growWord P 0 D p)))

theorem honest (simple:G.Simple)(o:Loc G 1)(N h j:ℕ)(live:j+h≤N)
    (v:Letter (R.family.labels.level d))(p:Scroll D):Auth d (ledger R u depth N h j v p):=by
  induction h generalizing j v p with
  | zero=>
    have top:=Roof.topC o (R.family.labels.level d) (R.family.localSection d) R.family.params
      (R.makes.sections d) (Next.Foundations.valuation G d) depth
    exact WilsonPointChildFoldedField.original (clef_through (top.officers v) (slotsFits _ v)) _
  | succ h ih=>
    apply Auth.sum
    intro s _
    apply WilsonPointChildEra.checked
    apply Auth.μ
    exact (ih (j+1) (by omega) _ _).verse _ (by omega) simple R.alloy.B.ratio

theorem original (simple:G.Simple)(o:Loc G 1)(price:ℕ→Gear G→ℝ)
    (paid:FundedMarkedCoverRows.prices price R.kit)(N h j:ℕ)(live:j+h≤N)
    (v:Letter (R.family.labels.level d))(p:Scroll D):
    (∀n,(ledger R u depth N h j v p).1 n=WilsonPointChildFiniteReturn.table R u depth tags N h j v p n) ∧
      (ledger R u depth N h j v p).2=WilsonPointChildCoverReturn.table R u depth N h j v p:=by
  induction h generalizing j v p with
  | zero=>exact ⟨fun _=>rfl,rfl⟩
  | succ h ih=>
    let V:=R.family.path.levels
    let P:=WilsonCoeffUV.loose V j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth (fun _=>0) N j
    let x:=growWord P 0 D p
    let upper(s:Letter (R.family.labels.level d)):=ledger R u depth N h (j+1) s x
    let fired(s:Letter (R.family.labels.level d)):=verseI V R.metals.O j N d (upper s)
    let row(s:Letter (R.family.labels.level d)):Era G ℝ:=
      WilsonPointChildEra.funded ((T⁻¹) s v) ((P.L.val:ℝ)^d • fired s)
    have hz(s:Letter (R.family.labels.level d)):Auth d (upper s):=honest R u depth simple o N h (j+1) (by omega) s x
    have hs(s:Letter (R.family.labels.level d)):Auth d (fired s):=
      (hz s).verse V (by omega) simple R.alloy.B.ratio
    have paidrow(s:Letter (R.family.labels.level d)):Auth d (row s):=WilsonPointChildEra.checked ((hs s).μ _) _
    have eqn(s:Letter (R.family.labels.level d)):=ih (j+1) (by omega) s x
    constructor
    · intro n
      have all:=honest R u depth simple o N (h+1) j live v p
      have print:(ledger R u depth N (h+1) j v p).1 n=
          rancho (flash ((ledger R u depth N (h+1) j v p).1 n)):=by
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
      have fine:(upper s).1 (n*(Next.Free.destination V N j).patch.L)=_ := (eqn s).1 (n*P.L)
      rw [show (fired s).1 n=_ from WilsonMarkedFiniteIndependentStep.original R u tags simple price paid N j d (by omega) (upper s) (hz s) n,fine]
      rw [←Nat.cast_pow,Nat.cast_smul_eq_nsmul ℝ]
    · change (∑s,row s).2=_
      rw [Prod.snd_sum]
      apply Finset.sum_congr rfl
      intro s _
      funext e r
      change (affix ((T⁻¹) s v) ((P.L.val:ℝ)^d • (fired s).2)) e r=_
      rw [show (fired s).2=_ from WilsonMarkedCoverIndependentStep.original R u tags simple price paid (N:=N) (j:=j) (by omega) d d le_rfl (upper s) (hz s) o,(eqn s).2]
      simp only [affix,Kemp.surf,Finset.sum_apply,Pi.smul_apply]
      rfl

end YM.Integration.WilsonPointChildPairedHistory
