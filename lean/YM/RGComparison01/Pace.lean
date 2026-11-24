import YM.RGComparison01.Rights
/-!
# Enter actual timetable to BELOW post-consistency of pencils

 Collect on auxiliary periods matching this caller's pitches, using the
 genuine scale trajectory, gathering conditional quotient estimates ALSO
 under the genuine aux V boundary here. Transfer derivatives by rental
 later. This supplies pencils from output Taylor/uncut tasks with shape
 uniformity. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Push.AbsoluteSums.Animals Slide Tensor WilsonStartup Bouquet Push.PriceCompiler
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves
open RG.Supply Shoot Input Org Ovens Progress.DirectedRecipe Next.Scheduling Further.PhysicalPeriodLimitF933
open Vision Studio Ports Starlight
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
namespace Pace
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A) (P : Sponsor G)
variable {c f : Side} {i m N k n : ℕ} {α β v p w : ℝ}
local notation "J" => (A.B.a.clock.J (m+1))
local notation "I" => (A.B.a.clock.J m)
local notation "B" => (A.B.a.budget m)
local notation "W'" => (A.B.a.budget (m+1))
local notation "Y" => X.p.profile I
local notation "Y₁" => X.p.profile J
local notation "L" => D.L J
local notation "Z" => F.target J I
local notation "t" => A.B.a.clock.hatBeta m
local notation "U" => RG.Rep G
-- defs for API
abbrev Annex (m k:ℕ) := Studio.Workshops F.shape P (A.B.a.clock.J m) (A.B.a.clock.J (m+1)) k (A.B.a.clock.adm (m+1)) (Rights.eta (A.B.a.clock.J (m+1))) (A.delay.betaEntry (A.B.a.clock.J (m+1)))
abbrev lay (m k:ℕ) := P X D F.target (A.B.a.clock.J m) (A.B.a.clock.J (m+1)) k
abbrev sk (m k:ℕ) := Rights.sky P F.target (A.B.a.clock.J m) (A.B.a.clock.J (m+1)) k D
abbrev cities (m k:ℕ) := Trio.fence (sk F P m k) (radiusB (A.B.a.clock.hatBeta m))
abbrev wide (m k:ℕ) := Trio.base (sk F P m k) (radiusB (A.B.a.clock.hatBeta m))
abbrev width (m k:ℕ) := (lay F P m k).stencil * radiusB (A.B.a.clock.hatBeta m)
abbrev job (m k:ℕ) := let p:=lay F P m k; nBudget p.inRank p.outRank (X.p.profile (A.B.a.clock.J m)).order k
variable (X': Pace.Annex F P m k)
abbrev doors := (lay F P m k).counts (sk F P m k) X'.uS X'.r X'.waits
local notation "A'" => X'.Staffer t (A.B.valid.pays m)
local notation "z" => doors F P X'
local notation "T'" => (lay F P m k)
local notation "S'" => sk F P m k
abbrev cut := Sienna.wick G (D.L (A.B.a.clock.J (m+1))) X'.uS (A.B.a.clock.hatBeta m)
abbrev reach (β:ℝ) := X'.r (A.B.a.clock.hatBeta m)*gStep β
abbrev faith (x:ℝ) := Loads.rateP (sk F P m k) k (lay F P m k).outRank (lay F P m k).inRank (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (doors F P X') X'.E₀ X'.r X'.tP |Pane.cloak D (A.B.a.clock.J (m+1))| x
abbrev costs (x:ℝ) := Loads.salary (sk F P m k) k (lay F P m k).outRank (lay F P m k).inRank (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) (doors F P X') X'.E₀ X'.r X'.tP |Pane.cloak D (A.B.a.clock.J (m+1))| x
local notation "r" => reach F P X' β
local notation "D'" => cut F P X'
local notation "b" => gStep β
include F P X'
lemma horizon (hp : β∈band A.B.a (m+1)) : 0<β ∧ 1 < X'.r t ∧ furl G (L) t < r ∧ 0 < furl G (L) t ∧ r ≤ 1 ∧ Sluice.Shore G L (Y).order t r ∧ Sluice.Health G L (Pace.wide F P m k) t r ∧
     costs F P X' t * b^(k+1) ≤ b^((k+1:ℕ)-Rights.eta J : ℝ) := (A').periods β (by rw [← PriceCompiler.beta_eq A.B.valid]; exact hp)

variable (H : f.val=c.val*(A.B.a.S.block m).val)
   (J' : Forest (Pane.panel A m H).ratio)
local notation "a" => Sienna.wick -- disable
local notation "K" => (Pane.panel A m H)
local notation "T" => Pane.orchestra A N H
local notation "q" => Mural.sheet X.p D (A.B.a.clock.adm (m+1))
set_option quotPrecheck false
local notation "φ" => A.B.kin.alpha N m
local notation "Kp" => (Trio.paySide G L S' t:ℝ)

omit P X' F in
lemma shins (m : ℕ) {c f : Side} (H : f.val=c.val*(A.B.a.S.block m).val) : (Pane.panel A m H).patch=Mural.sheet X.p D (A.B.a.clock.adm (m+1)) ∧ (Pane.panel A m H).kernel=X.p.kernel:= by
  let P' := (Pane.panel A m H).patch
  have h': P'= Mural.sheet X.p D (A.B.a.clock.adm (m+1)):= by
    cases h : P' with
    | mk d j h₁ hm hv =>
      have hh:j=A.B.a.clock.J (m+1):= by rw [← show (Patch.mk d j h₁ hm hv).J=j from rfl, ← h]; rfl
      have hp:d= D.L (A.B.a.clock.J (m+1)):= by rw [← show (Patch.mk d j h₁ hm hv).L=d from rfl, ← h]; exact PriceCompiler.block_eq A.B.valid m
      subst d j; rfl
  exact ⟨h',A.B.valid.kernel⟩

abbrev Pre (F:Roost.Factor A) (P:Sponsor G) (X' : Pace.Annex F P m k) (H : f.val=c.val*(A.B.a.S.block m).val) := warm X'.before (shins (A:=A) m H).1 (shins (A:=A) m H).2

variable (I' : Boulevard.Chartlet F.shape A N m H (Pane.virgin (Pane.orchestra A N H) (A.B.a.budget (m+1)) β))

omit X' in
include I' in
lemma aged (i : Slide.Stars) (he : c=Pace.cities F P m k i): Quilt (T) J' Kp := Trio.quilt G L S' t K T J' (he.symm ▸ Trio.taller ..) I'.laws.data.funds.length_eq I'.laws.data.room.larger

lemma tariffs (hm:m<N) : (T).up.Bounds (Y₁).clip (Y₁).width (Y₁).paths (ConnectedActivityE6.loopBill G L t) ∧ (T).down.Bounds (Y).clip (Y).width (Y).paths (ConnectedActivityE6.loopBill G L t) := by
  let V:= A.B.a.clock; let χ:= V.hatBeta m
  have hκ:= (A').wave
  have hA₁:V.hatBeta (m+1)= Pressure.betaF G χ L:= PriceCompiler.beta_eq A.B.valid m
  have hB' : V.loopCap (m+1) ≤ ConnectedActivityE6.loopBill G (L) t:= by
    have hp:= Pane.coverBill A.B.a (m+1)|>.2; apply hp.trans_eq; change 2*V.monitor (m+1)=2*Delay.fineMonitor G (L) _; unfold Calendar.monitor Delay.fineMonitor; rw [hA₁]; rfl
  have hB: V.loopCap m ≤ ConnectedActivityE6.loopBill G (L) t:= (Pane.coverBill ..).2.trans (Pane.brace _ hκ)
  rw [← params_eq A.B.valid m, ← params_eq A.B.valid (m+1)]; have h':= A.B.support.cap _ _ hm; have hX := A.B.support.cap _ _ hm.le
  exact ⟨{h' with two:=budget_loosen h'.two hB'}, {hX with two:=budget_loosen hX.two hB}⟩

lemma placement (hm:m<N) (hf:Quilt T J' Kp): ∃ ρ,(Pre F P X' H).Service J' (T).high (T).up ρ∧ ClassicalMatch J' (T).high (T).low (T).up (T).down ρ:= by
  obtain ⟨ρ,hρ,hX,hM⟩:=Pane.presents D A F.floor hm H J' («Y»:=fun _ _ _=> Kp) hf
  have hV : (T).up.Bounds (T).high (Y₁).width (Y₁).paths (ConnectedActivityE6.loopBill G L t):= by
    rw [show (T).high=(Y₁).clip from congr_arg RG.Stage.clip (params_eq A.B.valid (m+1))]; exact (tariffs F P X' H hm).1
  obtain ⟨v,hv⟩:= (Pre F P X' H).graph J' hV hf.large rfl rfl
  exact ⟨v,hv,(Pane.payouts (R:=T) (Before.Service.is_extension hv hρ) hX hM).1⟩

local notation "f₀" => (K).Choices
local notation "Xs" => Positions (Uniform.Primary c G)
section work
variable (ρ: Bid.Dir G c→ AxisChart G J')
include X' F P H J' I'
lemma assembled (hm:m<N) (ht:Quilt T J' Kp) (hβ:β∈band A.B.a (m+1)) (hρ:(Pre F P X' H).Service J' (T).high (T).up ρ) (hC : ClassicalMatch J' (T).high (T).low (T).up (T).down ρ)
    (i:f₀) (E' : Poll.Body (Precision.Key J' G)→ℝ×Positions (Uniform.Primary c G)→ℝ) (e:Config G f→ℝ)
    (hE : Probe E' (job F P m k) (z).letters ((T').inRank+1) r D' ((z).f t) ((z).f t))
    (he : Render J' ρ W' β e E' (T').inRank r D' (z).const)
    (x:Xs) (hx:‖x‖+furl G L t < r) (hV: flags (B).threshold (Boulevard.actual x)=∅) :
    Pushed X.O T J' i ρ W' β e E' k (job F P m k) (Y).order (T').inRank r⁻¹ (X'.aP t) (X'.tP t) x:= by
  obtain ⟨hc,hp⟩:= tariffs F P X' H hm
  let Θ:= Greenbelt.prism (T) t Chi.canonical (F.shape.o J I).K (Boulevard.actual x) J'
  have hh:= (A').crossing c f (K) (T) J' (shins (A:=A) m H).1 (shins (A:=A) m H).2 ht (congr_arg RG.Stage.clip (params_eq A.B.valid (m+1))) (congr_arg RG.Stage.clip (params_eq A.B.valid m)) hc _ hp ρ hρ hC i Θ rfl rfl hV.symm (W') B _ β I' rfl hV (horizon F P X' hβ).2.1 x rfl hx E' e hE he
  rw [F.settles J I] at hh; exact hh
end work
end Pace
end YM.RGComparison01
