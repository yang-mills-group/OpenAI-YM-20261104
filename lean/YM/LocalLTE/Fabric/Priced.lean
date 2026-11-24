import YM.LocalLTE.Bonnet.Quiet
import YM.LocalLTE.Rate.Season
import YM.LocalLTE.Rate.Permit
/-! Curve witness & receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
structure Trail (p:ℕ) where
   footprint : ℕ→ℕ→ℕ
   nextFloor : ℕ→ℕ→ℕ
   deep (j i:ℕ): StepStages j i→ footprint j i≤ nextFloor j i
   enough : ∀ j:ℕ,2* Coup.CeilingExtent nextFloor j ≤ (D.L j).val
   must j i : StepStages j i → wire H.w.ℓ ((R.target j i).halo) ≤ footprint j i
   κT : ℕ→ℕ→ℕ→ℕ
   penny : ℕ→ℕ→ℝ
   ψ : ℕ→ℕ→ℝ
   income : ∀ j i,0 < ψ j i ∧ ψ j i ≤ Time.credit G (X.p.profile i)
   pay : Sunshine H.w D R.shape penny ψ footprint p κT H.κ A.delay
   pew : Roof.PewT R.v R.t R.prices R.recordP R.span R.shape (Roof.wind R.menu) A.delay penny
   ambition : ∀ i j,(R.expense j i).wanting=-(7/16:ℝ)
variable {p:ℕ} (W : Trail H p) (hm:m<N)
variable {R₁:Rep G (A.B.a.S.side (m+1) n)}
    (hV: Lives A.B.bake N (m+1) n R₁)(hx:R₁.beta∈ band A.B.a (m+1))
    (U: Guide A.B R.shape N m n R₁) (hU:Opera.Price A.B R.shape N m n R₁ U)
namespace Trail
abbrev mass (m:ℕ):ℝ := W.penny (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
abbrev crew (m:ℕ):ℕ := W.footprint (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
abbrev lease (m:ℕ)(k:ℕ):ℕ:= W.κT (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) k
abbrev hop (m:ℕ):ℝ:= W.ψ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
abbrev extent (m:ℕ):ℕ:= Coup.CeilingExtent W.nextFloor (A.B.a.clock.J m)*(A.B.a.budget m).B
local notation "L'"=> D.L J
local notation "A'"=> A.B.a
local notation "ξ"=>betaF G x₀ L'
local notation "J'"=> X.p.profile I
local notation "µ"=>Coup.monthly (G:=G) (D.L J) x₀ (3*(W.mass H m))
local notation "κ"=> W.crew H m*radiusB x₀
-- Local permit inputs. Tag budget wiring.Plaw. Use independent F tables.
abbrev Hired (V:Rep G (A.B.a.S.side (m+1) n))(f:ℕ→ℕ) : Prop:= Coup.License p V H.κ ((A.B.a).clock.hatBeta (m+1)) f (W.extent H (m+1))
variable {tag:ℕ→ℕ}
variable (hl : W.Hired H R₁ tag)
lemma aware : 0 < W.hop H m ∧ W.hop H m ≤ Time.credit G (A.B.a.params m):=by
   rw [params_eq A.B.valid m]; exact W.income _ _
lemma earned : Coup.Clear H.w D R.shape W.penny W.ψ W.footprint p J I x₀ (W.κT J I) H.κ:= W.pay.clear _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)
include hV hx hl hm
lemma estate : East.Voices U B O (µ) (fun i=>East.bloom (betaF G x₀ L') (tag i)):= by
    have hP:= step_paid A.B.a m
    have h:= R.pledging
    have hf:= h.agenda _ _ hP|>.1
    have he:= R.pledging.agenda
    obtain ⟨hi,hj,hk,hP'⟩:= Rain.jersey (A:=A) (m:=m)
    let F i:=East.bloom (ξ) (tag i)
    have hM:= hl.bills
    have hg:Pumps R₁ F (1*incomingE G L' x₀):= by
        have hz:0<ξ:= zero_lt_one.trans_le (H.vote.cash _ _ hP|>.2 _ (A.B.valid.pays m)|>.light.1)
        rw [PriceCompiler.beta_eq A.B.valid] at hM; rw [one_mul,Coup.e_now _ _ hz,← Coup.chip_zero]; exact hM
    have ht:= Trail.earned H W (m:=m)
    apply East.voyage U B O µ _ _ _ ht.voices (show _ from Eq.trans_le (congr_arg (fun x:ℝ=>x+3) hk) hf) F hg.1 (Roof.defray R.pledging.conducts R.pledging.agenda hm hV hx U W.pew F hg ht.lineage)
end Trail
end YM.PhysicalNext.Repeat.Mallow
