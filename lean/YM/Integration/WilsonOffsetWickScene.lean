import YM.Integration.WilsonOffsetCompensatedGraph
import YM.Integration.WilsonOffsetLampRoster
import YM.Integration.FVA1Physical.Wilson.FluctuationMasks

/-! On one originally funded actual forest and step the two cutoff positions
are tested by their own original finite Wick rules. A separate root may be
used for the finite foreground at each location; positions are not rounded. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetWickScene
open Function Filter Finset Lattice Wilson RG Precision Tree Pressure
open PhysicalNext.Repeat.Legato MSbar MSbar.Lis MSbar.Mosaic MSbar.Bulk
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open RGComparison.Core16 RGComparison.Core16.Spool
open WilsonConditionalTaylorLabels WilsonOffsetLampRoster WilsonOffsetFittedPrimary WilsonOffsetOrderPayment
open MSbar.Midpoint Push.Uniform MSbar.Rolling
open scoped Classical BigOperators
variable {G:Gauge}

def degree (R:Run G) (d k:ℕ):ℕ:=k+order (R.family.labels.level d)+1

def bank (R:Run G) (d k:ℕ) (A:MSbar.Mosaic.Issue G) (Z:Positions (Primary A.c G)) (y:Site A.f)
    (i:(R.family.labels.level d).Index) (b:Bool) : ℝ :=
  let p:=degree R d k
  MSbar.Bakery.taste p (bulkColumn A R.metals.O (A.fClock • Z)
    (jointFieldBank (line i) A (fun _=>y) b) p) A.fClock

theorem earned (R:Run G) (u:G.ColorIndex) (rows:∀ a:Roster G,FluctuationMaskReadings (lamps a) R u)
    (d k:ℕ) (D:ℝ) (hD:0≤D) :
    let H:=degree R d k
    ∀ᶠ m:ℕ in atTop, ∀ N n, (hm:m<N) →
      (∃ S:Scene R.family.path.levels n (H+2),Realized R.alloy.B.kin N n m (H+2) (Lis.sun G u) S) ∧
      ∀ (S:Scene R.family.path.levels n (H+2)) (ready:Realized R.alloy.B.kin N n m (H+2) (Lis.sun G u) S),
        let F:=(ready.step m hm le_rfl).choose
        let v:=(ready.step m hm le_rfl).choose_spec.choose
        let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
        let y:=R.family.path.levels.clock.hatBeta (m+1)
        ∀ Z:Positions (Primary A.c G), ‖A.fClock • Z‖≤D*Heath.Cottage.room y →
          ∀ o:Site A.f,due R N n m d k o (postcard G A.c A.fClock Z) (bank R d k A Z o) :=by
  let H:=degree R d k
  let L:=radius G d
  have sold (i:(R.family.labels.level d).Index) :=
    rows (row i) H 6 L (by norm_num) D 1 hD zero_lt_one
  filter_upwards [eventually_all.mpr sold] with m all N n hm
  refine ⟨((all 0) N n hm.le).1,?_⟩
  intro S ready
  dsimp only
  intro Z hZ o
  dsimp only [due]
  intro i b
  let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S (ready.step m hm le_rfl).choose
    (ready.step m hm le_rfl).choose_spec.choose
  let y:=R.family.path.levels.clock.hatBeta (m+1)
  have hlog:0<Real.log y:=Real.log_pos (R.family.path.levels.fits.delayed (m+1))
  have size:0<closeN y:=pow_pos (Nat.ceil_pos.mpr (sq_pos_of_pos hlog)) _
  have witness:=((((all i) N n hm.le).2 S ready m le_rfl hm).2 o Z hZ (card i) b)
    (fun _=>o) (collar i o (closeN y) size)
  change |expect A.S A.pre (postcard G A.c A.fClock Z)
    (fun U=>look b (tally (line i) (fun _=>o) U))-bank R d k A Z o i b|≤A.fClock^((H:ℝ)+1-1) at witness
  simp only [literal,add_sub_cancel_right,Real.rpow_natCast] at witness
  exact witness

end YM.Integration.WilsonOffsetWickScene
