import YM.Integration.FundedCorrectedPeriod
import YM.RG01Estimate.SyntaxVac
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null

/-! Original curvature-packet addresses and actions, billed for the spatial
support exponent used before the measured reset. Changing the credit does
not change a packet, its original field, or its index in the complete list. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPeriodEntries
open Function Finset Lattice RG Wilson Marker WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat RG01Estimate IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Push.AbsoluteSums
open Comparison.Density
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

def tally (rows:List (Piece G n))(k:ℕ → ℕ → ℝ):Activities G n :=
  Render.adorn (fun a=>k a.power a.rank) (Pane.pale n G) rows

def quote (rows:List (Piece G n))(k:ℕ → ℕ → ℝ):ℝ:=
  Render.dollars (fun a=>‖k a.power a.rank‖) rows

private theorem valid {rows:List (Piece G n)}{B:BudgetPoint}(permits:Render.permits rows B)(k:ℕ → ℕ → ℝ):
    (tally rows k).Valid B (quote rows k) 0:=by
  induction rows with
  | nil=>exact Pane.whey n G B
  | cons a rows ih=>
    have tail:=ih (Render.seated permits)
    have both:=Payload.payment (k a.power a.rank) (Render.first permits) tail
    change (a.packet.attach (k a.power a.rank) (tally rows k)).Valid B (‖k a.power a.rank‖*a.credit+quote rows k) 0
    rw [add_comm]
    exact both

private theorem hard (rows:List (Piece G n))(k:ℕ → ℕ → ℝ):
    (tally rows k).forced=(Pane.pale n G).forced ∧ (tally rows k).K=(Pane.pale n G).K:=by
  induction rows with
  | nil=>exact ⟨rfl,rfl⟩
  | cons a l ih=>exact ih

def entries (n:Side)(B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(k:ℕ → ℕ → ℝ):Activities G n :=
  tally (Z.map (FundedCorrectedPeriod.piece n B σ C)) k

theorem same (B Q:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(k:ℕ → ℕ → ℝ):
    entries n B σ C Z k=entries n Q σ C Z k:=by
  induction Z with
  | nil=>rfl
  | cons a l ih=>exact congrArg ((FundedCorrectedPeriod.piece n B σ C a).packet.attach (k a.grade (a.rise+2))) ih

theorem original (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:preExponent B / B.B ≤ σ/4)(blocks:2 ≤ B.B)
    (Z:SeriesA G)(draw:Draw Z σ C)(k:ℕ → ℕ → ℝ):
    let A:=entries n B σ C Z k
    let bill:=quote (Z.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)) k
    Meadow.Budget B A.reg A.E bill ∧
    (∀s b, Nonempty (Caddy.Mirrors A.reg s b A.E)) ∧
    A.RegularFamily B ∧ A.forced=(Pane.pale n G).forced ∧ A.K=(Pane.pale n G).K:=by
  intro A bill
  have base:=(Pane.whey n G (Song.headline B)).moves
  have permit:=FundedCorrectedPeriod.permits Z draw simple hn (Song.headline B) hs reach blocks
    (Pane.pale n G) (fun s b=>(base s b).some)
  have live:(entries n B σ C Z k).Valid (Song.headline B) bill 0:=by
    rw [same (n:=n) B (Song.headline B) σ C Z k]
    exact valid permit k
  obtain ⟨cost,derivatives,anchored⟩:=live.boundE
  have reg:A.RegularFamily B:=by
    refine ⟨fun i=>?_,live.regular.at_flat,live.regular.vanish⟩
    have t:=live.regular.smooth i
    exact ⟨t.sites,t.borel,t.symmetry,t.smooth,t.hasDerivs⟩
  refine ⟨⟨cost,Song.enhanced B _ _ _ anchored,fun i=>⟨reg.smooth i,derivatives i⟩⟩,?_,reg,hard _ _⟩
  intro s b
  let p:=(live.moves s b).some
  exact ⟨⟨p.ep,p.reg_site,p.reg_support,fun i=>funext (p.valuesE i)⟩⟩

end YM.Integration.WilsonVacuumPreResetPeriodEntries
