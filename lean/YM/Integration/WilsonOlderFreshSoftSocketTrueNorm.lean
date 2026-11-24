import YM.Integration.WilsonOlderFreshSoftSocketFitted
import YM.Integration.WilsonOlderFreshSoftSocketNorm
/-! The charged measured physical entrance on the complete independently continued ordinary face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketTrueNorm
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketTotal (figure normalized cost)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats)
open WilsonOlderFreshSoftFigureReading (reading)
open WilsonOlderFreshSoftRoseCourse (grade seat)
open WilsonOlderFreshSoftRoseMarket (Probe row)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedFixedDigitHistory ActualRunPhysicalPages Pert.Asymptotics
variable {G:Gauge}(R:Run G)
local notation "L_" => R.family.path.levels
local notation "O_" => R.metals.O

open WilsonOlderFreshSoftSocketCensus (fee)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketFare (bracket)
open WilsonCoeffUV.Winding
open WilsonIndependentCollarOrdinaryCruise
open WilsonIndependentCollarOpticalTrial

open Filter WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshSoftTrialCharge (wages power bill)
open WilsonOlderFreshSoftSocketOptical (fixed)
open WilsonOlderFreshSoftSocketPaidRose (basis Sold Measured)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonOriginalPublicTrialInput (fitted vector)

def deposit (p:ℕ)(D:Fin 3→ℕ)(V:Realm G (p+1) Credit.leanC)(t:Finset (Fin 3))
    (draw:V.draws=R.family.path.levels)(N per K c v:ℕ)
    (a:Probe D V t)(w:(i:Fin 3)→R.family.label (grade i)):ℂ:=
  let d:=grade ∘ seat t
  let cells:=cast (congrArg (fun l=>Digits l t) draw) a.digit
  let w':=fun i:t=>w (seat t i)
  normalized R d a.coeff a.phase N per K c v cells univ w' a.root a.test p (regulatorRun R.family N per v)

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(D:Fin 3→ℕ)
    (p:ℕ)(A δ:ℝ)(A0:0≤A)(δ0:0<δ):
    ∃k:ℕ,∀(t:Finset (Fin 3)),t.Nonempty→∀(v:ℕ),k≤v→∀(j:Fin 3→ℕ),(∀i,k≤j i)→
      (∀i,(R.family.path.levels.budget (j i)).supportExponent≤100)→
      ∀(N per K c:ℕ),v≤c→c≤K→K<N→v+1≤K→2≤R.family.path.levels.clock.hatBeta K→
      R.family.S.scale K-R.family.S.scale v≤A*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1)))→
      (regulatorRun R.family N per K≤1) → (regulatorRun R.family N per v≤1) →
      ∀(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels),V.paid=R.metals.O→
      V.y=zz R.family.path.levels→V.anchor≤v→Dormitory V (mass (grade ∘ seat t) univ) 0 Credit.leanC→
      ∀(probe:Probe D V t)(order:ℕ)(η:ℝ)(M:Fin 3→ℝ)
        (Y:∀i:Fin 3,ℕ×ℕ→R.family.label (grade i))(before:∀i,j i≤K)(reg:Indexed R grade j order η M Y),
      0≤η→(∀i,0≤M i)→∀(income m C D₁ D₂:Fin 3→ℝ),
      let x:=regulatorRun R.family N per K
      let s:=Real.log x⁻¹
      let w:=fitted R grade j K order η M Y before reg N per
      (∀i,0≤ income i)→(∀i,M i≤C i*Real.exp ((2*m i)*s))→
      (∀i,Real.log (R.family.S.a K/R.family.S.a (j i))⁻¹≤D₁ i*s)→
      (∀i,income i≤Real.exp ((grade i:ℝ)*D₂ i*s))→
      (∏z:t,income (seat t z))*‖deposit R p D V t draw N per K c v probe w‖≤
        (bill R grade (seat t) C*Real.exp (power R grade (seat t) m η D₁ D₂*s))*
          (fee R (grade ∘ seat t) univ*(‖probe.test‖*(fixed R (D ∘ seat t)
            (grade ∘ seat t) p univ*x⁻¹^δ))):=by
  classical
  choose f book using fun t:Finset (Fin 3)=>eventually_atTop.mp
    (WilsonOlderFreshSoftTrialCharge.original (ι:=t) R simple shop grade)
  choose o travel using fun t:Finset (Fin 3)=>eventually_atTop.mp
    (WilsonOlderFreshSoftSocketOptical.original R (D ∘ seat t) (grade ∘ seat t) p univ simple A δ A0 δ0)
  let k:ℕ:=(∑t,f t)+(∑t,o t)
  refine ⟨k,?_⟩
  intro t occ v kv j kj support N per K c vc ck live vk warm span narrow cold V draw paid soft anchor dorm
    probe order η M Y before reg η0 M0 income m C D₁ D₂ x s w pos cap stretch roles
  have fo:f t≤k:=(single_le_sum (f:=f) (fun _ _=>Nat.zero_le _) (mem_univ t)).trans (Nat.le_add_right ..)
  have oo:o t≤k:=(single_le_sum (f:=o) (fun _ _=>Nat.zero_le _) (mem_univ t)).trans (Nat.le_add_left ..)
  obtain ⟨Z,high,low,opt⟩:=travel t v (oo.trans kv) V anchor draw soft N per K c vc ck live.le vk span
  let d:=grade ∘ seat t
  let T:=D ∘ seat t
  let W:=(∏i:t,income (seat t i))
  let b:ℝ:=WilsonOlderFreshSoftSocketPaidRose.basis R d (fun i=>w (seat t i)) N per K
  let F:=fee R d univ
  have source:W*b≤bill R grade (seat t) C*Real.exp (power R grade (seat t) m η D₁ D₂*s):=by
    have heard:=book t (f t) le_rfl j (fun i=>fo.trans (kj i)) support K order η M Y before reg
      N per live warm η0 M0 (seat t) income m C D₁ D₂ pos cap stretch roles
    have entry:b=WilsonOlderFreshSoftTrialCharge.wages R grade j K order η M Y before reg N per (seat t):=by
      unfold b d WilsonOlderFreshSoftSocketPaidRose.basis WilsonOlderFreshSoftTrialCharge.wages
      apply Finset.sum_congr (by ext z;constructor <;> intro _ <;> apply Finset.mem_univ)
      intro b _
      congr 1
      unfold WilsonOriginalPublicTrialFigure.weight
      apply Finset.prod_congr (by ext z;constructor <;> intro _ <;> apply Finset.mem_univ)
      intro i _
      simp only [WilsonOriginalPublicTrialInput.vector,if_pos live,Function.comp_apply,w]
    rw [entry]
    exact heard
  have B0:0≤b:=sum_nonneg fun _ _=>norm_nonneg _
  have W0:0≤W:=prod_nonneg fun _ _=>pos _
  have F0:0≤F:=sum_nonneg fun _ _=>prod_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  let Vw:=fun i:t=>w (seat t i)
  letI : Nonempty t:=by
    obtain ⟨i,hi⟩:=occ
    exact ⟨⟨i,hi⟩⟩
  have θ0:0≤regulatorRun R.family N per v:=(ActualRunKernelPackets.regulator_pos R N per v (vc.trans (ck.trans live.le))).le
  have x0:0≤x:=(ActualRunKernelPackets.regulator_pos R N per K live.le).le
  have pay0:=WilsonOlderFreshSoftSocketOptical.fixed_nonneg R T d p univ
  have bound:=WilsonOlderFreshSoftSocketNorm.original R T d p univ Finset.univ_nonempty V draw paid dorm N per K c v
    anchor vc ck live.le narrow Z Z high low probe.coeff probe.phase Vw probe.digit probe.root probe.test
    (regulatorRun R.family N per v) (by rwa [abs_of_nonneg θ0])
  rw [WilsonOlderFreshSoftSocketPaidRose.salary] at bound
  calc W*‖deposit R p D V t draw N per K c v probe w‖≤
         W*((b*F)*(‖probe.test‖*gross R T d p univ Z Z)):=mul_le_mul_of_nonneg_left bound W0
       _ = (W*b)*(F*(‖probe.test‖*gross R T d p univ Z Z)):=by ring
       _ ≤ (W*b)*(F*(‖probe.test‖*(fixed R T d p univ*x⁻¹^δ))):=by gcongr;exact opt
       _ ≤ _:=mul_le_mul_of_nonneg_right source (by positivity)

end YM.Integration.WilsonOlderFreshSoftSocketTrueNorm
end
