import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Block
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Family
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Calendar
/-! # Window costs at H_r on every slot. G budget (one power sufficient to pay rounding
      arbitrary high in g; enough poly bound here). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ} {I:Type} {F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {x:I→Points n}{y:I→Points m}{r T:I→ℝ} (R:Room W c δ A B)
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge} {N : WilsonPrescription G} (ν:ℝ) {sim : G.Simple} {C : Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(Y:ℝ→tower S) (Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (H0: LogTrace U Q.port)
    (hY:Leading U Y)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ: MS.Land.Prescription (Press.portDeck G)} {dial:Bool}
    (H:Main.Match N sim M σ dial) {t:ℝ→ℝ}
    (S0:StepCost G (GroupS.ψ N.criterion M ν) (GroupS.gaugeN N.scheme N.criterion M ν) t (via Y))
    (ht: Calibrated G t)
    (h:Aim F G W a b r T)(hb:0<b) (hx:∀ᶠ i in F,x i∈A)(hy:∀ᶠ i in F,y i∈B)
    (u:Tags G d (n+m)) (v w : I → Viewers U)

local notation "s" => fun i:I=>r i*T i
local notation "e₀" => fun _ : Fin n=>d
local notation "e₁" => fun _ : Fin m=>d
local notation "Z₀" => joins
local notation "g" => (fun i=>g0 G (r i))
abbrev args (Y:ℝ→tower S)(d:ℕ)(r T:ℝ)(w : Tags G d m) : Tags G d m :=fun i=> via Y (r*T) r d (w i)
lemma bridge (o:Owner U) (r T:ℝ) (x:Points n)(y:Points m)(u:Tags G d n)(w:Tags G d m) :
    measures U Y e₀ e₁ o r T x y u w=total U Y e₀ e₁ o r T x y u (args Y d r T w):= by
  unfold total at_far; rw [adjusted_apply]; apply congr_arg; funext i; simp [args,via]
include H S0 ht h R hb
lemma be (d:ℕ) (w:Sec G d)(z:Toon G d): (fun i=> coord z (via Y (s i) (r i) d w))=O[F] Pose.home := by
  have he:∀ᶠ i in F,1≤T i ∧ T i≤ a*g0 G (r i)^(-b) := (aspirant R h).and h.bud
  have hn:∀ i j:Toon G d,(fun k=> columns (via Y (s k) (r k) d) i j)=O[F] Pose.home := matrixPay.mp ((ScaleCost.issued_norms ((H.dilation ν).check) sim (transition sim ht) hb (checks Y) S0 h.reach he (reflexive Y)).2)
  calc
    (fun i=>coord z (via Y (s i) (r i) d w)) = (fun i=> (columns (via Y (s i) (r i) d) *ᵥ numbers w) z) := funext (fun i=>Eq.symm (congr_fun (issued ..) z))
    _ =O[F] _ := IsBigO.sum («s»:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset (Toon G d)))=> Pose.mix_home (hn z i) (Pose.cpoint _))
lemma split_arg (v' :Tags G d m) : ∀ i:Fin m, ∀ j:Toon G d,
    Allowance F r Pose.home (fun k=> coord j (args Y d (r k) (T k) v' i)) := fun _ j=>Allowance.covers (be R ν Y H S0 ht h hb d _ j) -- order

include hx hy H0 hY
local notation "X" v:max => (fun i=> physicalY U Y (v i) u (r i) (joins (x i) (y i) (T i)))
lemma onRows : Allowance F r Pose.home (X v) ∧
    Allowance F r s (fun i=> (X v) i-(X w) i) := by
  let W₀:Tags G d n:= u ∘ Fin.castAdd m; let E:Tags G d m:= u ∘ Fin.natAdd n
  let V i := args Y d (r i) (T i) E; let p := fun (w:I→Viewers U) (i:I)=> trueY U Y (r i) (s i) 0 (w i) (d:=e₀) (e:=e₁) (x i).ofLp (y i).ofLp W₀ (V i)
  have eq (a:I→Viewers U): p a =ᶠ[F] X a := by
    filter_upwards [permit R h hx hy, h.reach.eventually self_mem_nhdsWithin] with i hi hr; change Orbits.whole _ _ _ _ _=_; rw [ ← show Original.total U Y e₀ e₁ (a i,0) (r i) (T i) (x i) (y i) W₀ (V i)=_ from total_eq .., ← bridge,illuminate U Y _ hi hr ]; congr 2; funext j; induction j using Fin.addCases <;> simp [W₀,E,Function.comp_apply]
  have T' : Tendsto s F late := view R h sim
  have hn: ∀ d:ℕ, FieldQuote G (GroupS.gaugeN N.scheme N.criterion M ν) t (via Y) d 1 := fun d=>S0.fields d 0
  have hE := split_arg R ν Y H S0 ht h hb E
  constructor
  · exact (Allowance.congr (f:=p v)
      (Original.worth U Y Q H hY hn H0 (hx:=pay R h hx hy) T' R.size R.clearance (u:=fun _=> W₀) (d:=e₀) (e:=e₁) (o:=fun _=>0) (fun i j=>Allowance.fixed _) hE v) (eq v))
  exact (split_phase U Y Q H hY hn H0 T' (o:=fun _=>0) R.size R.clearance (hx:=pay R h hx hy) (u:=fun _=> W₀) (v:=V) (d:=e₀) (e:=e₁) (fun i j=>Allowance.fixed _) hE v w).congr ((eq v).sub (eq w))

-- need pay poly price enough for first rounding. Later even all-order (for estimate after movement).
omit ht S0 H hY H0 hx hy hb
include sim

end YM.FVA2.GradedFar259.Flash
