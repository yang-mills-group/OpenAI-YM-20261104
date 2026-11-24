import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Rest
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Coffer
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Opera
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Gates
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Venue


set_option autoImplicit false
noncomputable section

namespace YM.RG.Shoot
open Lattice Wilson RG.Supply
structure PartialLives {G:Gauge} {a:Levels G} (O : Recipe a) (N m n) (u : YM.RG.Rep G (a.S.side m n)) : Prop where
  path : u.path=O.path N m
  point : u.p=a.budget m
  clip : u.clip=(a.params m).clip
  valid : u.Lawful (a.params m).width (a.params m).paths (a.clock.loopCap m) (a.clock.allowance m) (a.clock.forcedAllowance m)
end YM.RG.Shoot
namespace YM.ConnectedActivityE6
open Filter Lattice RG Pressure Pressure.Stores RG.Patch Wilson
open Push.SectorMeasure Presented Push.AbsoluteSums Reserves
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}

namespace Application
open Pressure.Testing RG.Supply RG.Shoot Precision YM.Input
variable {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Supply.Delays Θ}
variable {Y : Bar W} {I : Wait Y} {Z : ChartRatio G} {K : MapPrices} {Q : PostCost D}

lemma partial_intake (B : Directed G I Z K Q) (N m p : ℕ) (hm : m < N) (R : Rep G (B.a.S.side (m+1) p))
    (hL : PartialLives B.bake N (m+1) p R) (hB : R.beta ∈ band B.a (m+1)) :
    let i := B.a.clock.J m; let j := B.a.clock.J (m+1); let T := ships B N m p
    Intake (query C K j i) T (B.a.clock.hatBeta m) R := by
  intro i j T
  let t := B.a.clock
  let S := t.op m p
  let x := t.hatBeta m
  have he := clock_next B.a m p
  change t.hatBeta (m+1) = betaF G x S.patch.L at he
  have hh : (B.a.params (m+1)) = C.profile j := congr_fun B.valid.stage _
  refine ⟨proceeds B N m p hm,⟨?_,?_,?_⟩,?_,?_,he ▸ (B.a.fits.delayed (m+1)), ?_,?_⟩
  · rw [hL.path, B.bases]; rfl
  · exact hL.clip
  · change _=temp _
    rw [hL.point]; change t.threshold (m+1)=temp (betaF G x S.patch.L); rw [← he]; rfl
  · have hU : incomingK G S.patch.L x=t.forcedAllowance (m+1) := by
      unfold incomingK Delay.fineMonitor; rw [← he]; rfl
    have hF : incomingE G S.patch.L x=t.allowance (m+1) := by unfold incomingE; rw [← he]; rfl
    have hg : t.loopCap (m+1) ≤ loopBill G S.patch.L x := by
      unfold Calendar.loopCap loopBill Delay.fineMonitor; rw [← he]
      have he' := t.adm (m+1)
      have ht := B.a.fits.thetaRange (m+1)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [show Vac.Numbers.P (t.hatBeta (m+1)) = (t.monitor (m+1)) ^ (1:ℝ) by rw [Real.rpow_one]; rfl]
      apply Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _))
      refine ht.2.trans (inv_le_one_of_one_le₀ ?_)
      exact_mod_cast show 1 ≤ t.J (m+1) by omega
    refine ⟨?_,hU.symm ▸ hF.symm ▸ hL.valid.labels⟩
    change R.path.Bounds R.clip (C.profile j).width (C.profile j).paths (loopBill G S.patch.L x)
    rw [← hh]; exact { hL.valid.paths with two := budget_loosen hL.valid.paths.two hg }
  · rw [hL.point]; change (C.profile j).supportExponent=(B.a.params (m+1)).supportExponent; rw [hh]
  · rw [hL.point]; change t.coverSize (m+1) = radiusB (betaF G x S.patch.L); rw [← he]; rfl
  change betaF G x S.patch.L / 2 ≤ _ ∧ R.beta ≤ 2*betaF G x S.patch.L; rw [← he]; exact hB
end Application
end YM.ConnectedActivityE6
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees    PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} 

open RG.Supply Pressure.Testing
namespace Planning



open Input Shoot
variable {C : Sheet G} {M : MapPrices} {Q : ∀ j i,Target G (Pressure.Testing.query C M j i)}
variable {p : ∀ j i,Target.Expense (Q j i)} {D : Supply.Rolls C}
variable {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
variable {O : ChartRatio G} {K : PostCost D} (D' : Directed G I O M K)
variable {w : ℕ→ℕ→ℝ} {A : ℕ→ℝ} (L : Purchase C M Q p D w A) (he : A≤W.betaEntry)
variable (h : ∀ N m n,m≤N→ Sworn (D'.M.H N m) n G)
include L he



include h
lemma partial_walls (N m n : ℕ) (hm : m<N) (R : Rep G (D'.a.S.side (m+1) n)) (hR : PartialLives D'.bake N (m+1) n R) (hx : R.beta∈band D'.a (m+1)) :
    let j:= D'.a.clock.J (m+1); let i:= D'.a.clock.J m; let T:= ships D' N m n; let x:= D'.a.clock.hatBeta m; let P:=p j i
    ∃ (H : Cash (w j i) x (L.μ j i) (D.L j) (Q j i) (L.o j i) (L.c j i) T R), Cash.Renewed P.degrees P.earn P.one P.two H ∧
      (Q j i).mergeScale (D.L j) (L.μ j i) x P.degrees ≤ D'.a.clock.hatBeta (m+1)^P.wanting := by
  intro j i T x P
  have ⟨h1,h2,h3,h4⟩:= testing D' L he N m n hm
  have hv : SliceRows.Stamp T := ⟨D'.M.H N (m+1),D'.M.H N m,D'.plan.crossings N m n hm,D'.plan.stack N m n hm,h N _ _ hm,
    h N _ _ hm.le,D'.support.links _ _ hm,D'.support.links _ _ hm.le,_,_, D'.plan.all N _ hm _,_,_,D'.plan.all _ m hm.le _⟩
  obtain ⟨H,hH⟩:= (h4.2 _ _ _ _ h3).2 hv R (Application.partial_intake D' N m n hm R hR hx)
  rw [PriceCompiler.beta_eq D'.valid]; exact ⟨H,hH,h4.1⟩
end Planning
end YM.ConnectedActivityE6
namespace YM.PhysicalNext.Repeat.Opera
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}
    {E : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage} {w u : ℝ→ℝ} {f r b : Return.Wages}
    {q : UVNext.CouplingReset.ResetPrices} {η : ℕ → ℝ} {A : Scouts (F:=F)} {hL : ℕ→ℝ}
    {Q : Targets s K} {p : Expenses Q} {c : ℝ}
    (B : Directed G I Z K P) (R : Register D p f hL)

variable {N m n : ℕ}
variable (hm : m<N)
    (h : ∀ N m n,m≤N → Bid.Sworn (B.M.H N m) n G)
    (hr : Receiving R A W c)
    (hQ : ∀ j i:ℕ, StepStages j i → (s.profile i).supportExponent+3≤(p j i).earn)
    (M : Use.Machine B E A η q f r b) (ht : Treble W)
    {X X' : RG.Rep G (B.a.S.side (m+1) n)}

include h hr hm
lemma partial_feature (hl : PartialLives B.bake N (m+1) n X) (hb : X.beta∈band B.a (m+1)) : ∃ I : Guide B R N m n X, Price B R N m n X I := by
  obtain ⟨I,hI,hA⟩:= Planning.partial_walls B R hr.grow.1 h N m n hm X hl hb; exact ⟨I,hI⟩


end YM.PhysicalNext.Repeat.Opera
