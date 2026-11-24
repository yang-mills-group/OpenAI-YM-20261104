import YM.OPE.Compatible.Streams.Whip
import YM.OPE.Compatible.LevelX.Ela
/-!
# Continuum-wheel, with profile chosen once at common repeated cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Y"=> solar G d τ
open JetS
variable (H:LocalRatio R)(hs:G.Simple)(X:Sailing T P p R b)
variable (B:Medal P G K.K P.J)
variable {w:ℝ} (D₀:Stern K P τ l d w)(Hp: Crest G P K.K m)
local notation "V" => Fin (l+1)
local notation "S!"=>Sailing T P p R b
local notation "LQ"=> Quoin hs D₀ B H
local notation "Θ"=>Tracts G d τ →L[ℝ] Tracts G d τ
structure Topic (H: LocalRatio R)(hs:G.Simple)(X:Sailing T P p R b) (B:Medal P G K.K P.J)(D:Stern K P τ l d w) where
    station: Tracts G d τ→L[ℝ] Tracts G d τ
    r : ℕ→ℝ
    t : ℕ→ℝ
    bill (i:ℕ)(h:i<l+1): Crown (p:=p) (T:=T) (b:=b) H hs B D station (r i) (t i) i
variable {hs H X B D₀}
lemma arises (he: Crest G P K.K m)(hx:∀ i,τ i≤ m): Nonempty (Topic H hs X B D₀):=by
    let I:ℕ→ Fin (l+1):=fun i=>⟨min i l,by omega⟩; haveI : Nonempty (S!) :=⟨X⟩; obtain ⟨A,ha⟩:= framing (T:=T) (b:=b) (p:=p) hs D₀ B H he hx; choose r t hq using ha; refine ⟨A,r∘I,t∘I,fun i hi=>?_⟩; have he:= hq (I i); generalize hK:I i=j at he;have hi':j.val=i:=by
         rw [← hK]; dsimp only [I]; exact min_eq_left (by omega)
    subst i; unfold Function.comp; rw [hK]; exact he
namespace Topic
variable (T':Topic H hs X B D₀)
noncomputable abbrev At (v:S!):= Quoin hs D₀ B H v
include T' -- maybe omit
abbrev Mint (e:ℕ):= Fruition T'.station (lapPrice P.L e)
noncomputable abbrev Late (e:ℕ)(v:S!):=Lingo (T'.r e) (Quoin hs D₀ B H v)
abbrev LateEnd (e:ℕ)(v:S!):= Lingo (T'.t e) (Quoin hs D₀ B H v)
lemma StepHot (he:e+1<l+1)(a:S!):LateEnd T' e a= Late T' (e+1) a:=
    Eave.Shade_eq (G:=Bead G l) (T'.bill e (by omega)) a (T'.r _) (e+1) (Eave.chip (G:=Bead G l) (T'.bill e (by omega))) (Eave.slope (G:=Bead G l) (T'.bill (e+1) he))
lemma Verse (a:S!):T'.Late 0 a=⊤:= top_unique (fun i _=> (Eave.wheel (G:=Bead G l) a (T'.bill 0 (by omega)) i))
noncomputable def beam (e:ℕ)(he:e<l+1)(a:S!): Late T' e a→L[ℝ] Mint T' e:= Eave.PO (T'.bill e he) a
lemma liftU(e:ℕ)(he:e<l+1)(a:S!)(v:T'.Late e a) :T'.beam e he a v=0↔ v.val∈T'.LateEnd e a:= Eave.fruitsZ (G:=Bead G l) (T'.bill e he) a v
lemma LeanBudget (e:ℕ)(he:e<l+1): ∃ C:ℝ,0 ≤ C ∧∃ k:ℕ,∀ i:S!,∀ x:T'.Late e i,‖(T'.beam e he i x).val‖≤ C*i.cost^k*‖x.val‖:= Eave.OpFee (G:=Bead G l) (T'.bill e he)

end Topic
end YM.OPE.Stroke
