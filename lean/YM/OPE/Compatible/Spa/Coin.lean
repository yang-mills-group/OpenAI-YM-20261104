import YM.OPE.Compatible.Spa.Ara
/-!
# The phase shift on a filtered reading

`ReadK` composes a flag reading with the chosen coordinate map. With the `Bals`
and `Floss` compatibility data, `orbRuns` restricts `Gift` to each flag and shows
that `ReadK` carries this restriction to the coordinate shift `τΓ`.
`turn_nil` shows that three applications of `Gift` give zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
noncomputable abbrev ReadK (κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val))(U:Z.Ω M Y)(e:J!)(t:M): U.flag e.val t →ₗ[ℝ] Jewel (A' e.val):= (κ e).comp (U.read e.val e.isLt t)
local notation "F!"=> Tracts G d τ
section
set_option maxHeartbeats 200000 in
lemma Bals.shift {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(e:J!)(x:Mint Z e.val):κ e (WaneZ Z e.val e.isLt x)=τΓ _ (κ e x):=by
        apply Sleek.comm (E:= ↥(Fruition Z.station (lapPrice P.L e.val))) (F:= Jewel (A' e.val)) (σ:= (WaneZ Z e.val e.isLt).toLinearMap) (C.tricks e) _ (C.shares e).τZ (fun x=> (sprain Z e.isLt (A' e.val) x).symm) x
set_option maxHeartbeats 200000 in
lemma turn_nil (x:F!): Gift G D₀.aware (Gift G D₀.aware (Gift G D₀.aware x))=0:=by
       funext i; have hp(v:F!): Gift G D₀.aware (Gift G D₀.aware v) 1=0:=by rw[tack1 D₀.aware (Gift G D₀.aware v) 0 1 rfl,Jac.tack,map_zero]
       fin_cases i
       · exact Jac.tack ..
       · exact hp _
       change Gift G D₀.aware _ 2=0; rw [tack1 D₀.aware _ 1 2 rfl,hp x,map_zero]
private lemma restrictObserved {E V : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : Submodule ℝ E) (W : E →ₗ[ℝ] E) (f : A → A)
    (h : ∀ x, (f x).val = W x.val) (read : A → V) (turn : V → V)
    (hr : ∀ x, read (f x) = turn (read x)) :
    ∃ T : A →ₗ[ℝ] A, (∀ x, (T x).val = W x.val) ∧ ∀ x, read (T x) = turn (read x) := by
  let T := (W.comp A.subtype).codRestrict A (fun x => h x ▸ (f x).property)
  refine ⟨T, fun _ => rfl, fun x => ?_⟩
  have same : T x = f x := Subtype.ext (h x).symm
  exact (congrArg read same).trans (hr x)

lemma orbRuns {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(T':Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(e:J!)(i:M):∃ T: U.flag e.val i→ₗ[ℝ] U.flag e.val i, (∀ x,(T x).val=Gift G D₀.aware x.val)∧∀ x,ReadK Z κ U e i (T x)=τΓ (A' e.val : Type) (ReadK Z κ U e i x) := by
  choose f values readings using T'.turn e.val e.isLt i
  apply restrictObserved (U.flag e.val i) (Gift G D₀.aware).toLinearMap f values
    (ReadK Z κ U e i) (τΓ (A' e.val : Type))
  intro x
  exact (congrArg (κ e) (readings x)).trans (Bals.shift Hp Z a C e _)

end
end YM.OPE.Stroke
