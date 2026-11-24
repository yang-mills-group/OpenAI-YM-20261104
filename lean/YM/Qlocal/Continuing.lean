import YM.Qlocal.Program
/-!
 Repeat Kit relative norm and hit.Unrolls.R. Here carry any inherited
 marked data with its literal powers on any levels.W.P. booking. Includes
 full exact-step.V.Also allows strengthen by any Protocol interior.Throw with
 proof later. Use cumulative cost for estimating relative analytic model/errors on
 suitable intervals.No assertion that bandwidth at arbitrarily late cutoff
 retains all test-space/width grants under ANY directly stipulated operation; need
 further lemmas for root reassignment, mask changes, etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Program
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
variable {Ω ι V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge}{X:Metals G}{D:Rolls X.p}
    {Δ:ℕ→Prop}{A:Alloy X D}(F:Factor A){m k p N j k' z : ℕ} {δ r θ u v w E C : ℝ}
local notation "a"=> A.B.a
set_option quotPrecheck false
local notation "I"=> (a).clock.J m
local notation "J"=> (a).clock.J (m+1)
local notation "S"=> (a).clock.op m p
local notation "x₀"=> (a).clock.hatBeta m
open Frigus Scale
variable (Y₀:Org.Bolt A) (η:ℕ→ℝ)(H T:ℕ→ℕ)

variable {F η H T}
namespace Camp
open Scale
variable (Q : Camp F η H T)
include Q

open RG3
variable {Y₀}
-- State subset.
variable {R: (i:ℕ)→ RG.Rep G (A.B.a.S.side i p)}{P : ℕ→Floe.Layout G}{Γ : ℕ→ Floe.Pace.Coin}(p₀:JourneyK A F Y₀ P Γ z N p k R) -- `JourneyK`
    (o:(i:ℕ)→V→ Site (A.B.a.S.side i p)) (s:(i:ℕ)→ V→Support (A.B.a.S.side i p)) (u: V→ℝ) (c:B.Mode→ℝ) (j:ℕ) -- j top of interval
local notation "R★"=> fun i=> Taste Ω (o i) (R i) B
local notation "Ttl"=> rent u c
-- iteration step.Intent.owner after Epoch etc. `Food` carrier z' in Area.Extract.
variable {o s u c} [Fintype V] [Nonempty Ω][Nonempty V] (hC:Spirit c)(hu:∀ i,0 < u i)
    (Y:Taste Ω (o j) (R j) B)
local notation "Rᶜ"=> fun i=> R i
local notation "c★"=> fun m=>rent (shift (Q.scale m j) u) c
local notation "u★"=>fun m=> shift (Q.scale m j) u

-- allows additional Protocol. Separate opening closure if need. No oracle or assuming model.
abbrev Protocol (T':Levels G)(p:ℕ) (Ω:Type)(B:Marker.Census V)(R:(i:ℕ)→RG.Rep G (T'.S.side i p))(o:(i:ℕ)→ V→Site (T'.S.side i p)):= (m:ℕ) →Taste Ω (o m) (R m) B → Prop
variable (M₀:Protocol A.B.a p Ω B R o) (W₀:(m:ℕ)→Taste Ω (o m) (R m) B)
omit Q
variable (o s u c)
structure Trip (z:ℕ):Prop where
    begin : W₀ j=Y
    intern : ∀ i,z ≤ i → i ≤ j →
       let Z:= W₀ i; M₀ i Z ∧ (∃ d, RetainsDeclared d Z (s i)) ∧ Peak (R i) (o i) Z (rent (shift (Q.scale i j) u) c) (R i).p.supportExponent 1 1
    move : ∀ i,z ≤ i → i < j →
       let Z:=W₀ i; Peak (R i) (o i) Z (rent (shift (Q.scale i j) u) c) (R i).p.supportExponent 1 (Time.quoteHard A.B.a i F.book (R (i+1)).beta) ∧ ∀ x,(Z.leaf x).density=(A.B.a.clock.op i p).push ((R (i+1)).beta) ((W₀ (i+1)).leaf x).density
local notation "Z!"=> Trip (u:=u) (s:=s) (c:=c) (o:=o) Q -- check parameters via error; order.Work now explicit
omit [Fintype V] [Nonempty V] [Nonempty Ω] in
private def unclaimed {j:Side}(P:RG.Rep G j)(p:V→Site j)(Ω:Type)(B:Marker.Census V): Taste Ω p P B:= ⟨⟨p,fun _=> B.quiet,fun _=>∅,fun _ _=>B.quiet,0,0,0⟩,rfl,fun _=>B.quiet,fun _=>∅,0⟩

def Mechanism := ∀ i, z ≤ i → i < j →∀ W':Taste Ω (o (i+1)) (R (i+1)) B,
    M₀ (i+1) W'→
    (∃ d,RetainsDeclared d W' (s (i+1)))→ Peak (R (i+1)) (o (i+1)) W' (rent (shift (Q.scale (i+1) j) u) c) (R (i+1)).p.supportExponent 1 1 →
    ∃ K:Taste Ω (o i) (R i) B, M₀ i K ∧ (∃ d, RetainsDeclared d K (s i)) ∧ Peak (R i) (o i) K (rent (shift (Q.scale i j) u) c) (R i).p.supportExponent 1 (Time.quoteHard A.B.a i F.book (R (i+1)).beta)∧ ∀ x,(K.leaf x).density=(A.B.a.clock.op i p).push ((R (i+1)).beta) (W'.leaf x).density
variable (ht: Agenda (A:=A) o s z j) (hY: Peak (R j) (o j) Y (rent u c) (R j).p.supportExponent 1 1)
 (hh: ∃ d, RetainsDeclared d Y (s j))
-- m interval.Sp.
include p₀ Q
lemma lease_stand {i:ℕ}(hi:z ≤ i)(hf:i<N): Time.quoteHard A.B.a i F.book (R (i+1)).beta ≤ hardcap A.B.a T i:=
   (Q.fee i).2.2 _ ((p₀.1.walk (i+1) (by omega) hf).beta.symm ▸ (Y₀.sticks N p |>.prices (i+1) (by omega) hf).2)
include hY hh
lemma progress (hf: M₀ j Y) (he: Mechanism (z:=z) (M₀:=M₀) Q o s u c j)(hj:j ≤ N) {i:ℕ}(hi:z ≤ i)(hk:i≤j): ∃ W, Trip (s:=s) (Y:=Y) (c:=c) (u:=u) Q o j M₀ W i:= by
 induction hk using Nat.decreasingInduction with
 | self=>
    let W:=Function.update (fun i=>unclaimed (R i) (o i) Ω B) j Y; let he:W j=Y:= update_self ..
    refine ⟨W,he,fun i h w=> ?_, fun i v w=>by omega ⟩; rw [le_antisymm w h, he]; dsimp only; rw [show (shift (Q.scale j j) u)=u from (by funext i; simp [scale, Emissions.shift])]; exact ⟨hf,hh,hY⟩
 | of_succ m hx ih=>
    obtain ⟨W,hW⟩:= ih (by omega); obtain ⟨hz,h₁,hY⟩:= hW.intern (m+1) le_rfl hx; obtain ⟨Y',h1,hG,hK,hL⟩:= he m hi hx (W (m+1)) hz h₁ hY; let u':=Function.update W m Y'; have hp : u' m=Y':= update_self ..; have ht(i)(hi:m < i):u' i=W i:= update_of_ne hi.ne' ..; refine ⟨u',(ht _ hx).trans hW.begin,fun i hv he=> ?_, fun i hv he=>?_⟩
    · rcases lt_or_eq_of_le hv with hw|rfl; · rw [ht _ hw]; exact hW.intern _ hw he
      rw [hp]; exact ⟨h1,hG,hK.loosen le_rfl ((Q.lease_stand p₀ hi (hx.trans_le hj)).trans ((hip A.B.a T m).trans (reserve_bounds A.B.a m).2))⟩
    rcases lt_or_eq_of_le hv with hw|rfl; · rw [ht _ hw,ht _ (by omega)]; exact hW.move i hw he
    rw [hp,ht _ (m.lt_succ_self)]; exact ⟨hK,hL⟩
variable (h0:j ≤ N)
omit hh hY
include hu h0 hC ht
local notation "P0"=> (fun _ _=> True)
lemma basics : Mechanism (z:=z) (M₀:=P0) (R:=R) (Ω:=Ω) Q o s u c j:= by
 intro i hi hk W₀ H hW hl; obtain ⟨K,ht,hK,hV⟩:= Q.next p₀ u j hC ht hu h0 hk hi W₀ hl hW; exact ⟨K,trivial,ht,hK,hV⟩
include hY hh
lemma realistic (hi:z ≤ j): ∃ W, Trip Q o s u c j Y P0 W z:=
     Q.progress p₀ o s u c j Y P0 hY hh trivial (Q.basics p₀ o s u c j hC hu ht h0) h0 le_rfl hi
end Camp
end YM.Qlocal.Program
