import YM.Integration.FVA1Physical.TwoReset.StableRead
import YM.Integration.FVA1Physical.TwoReset.SoleMass

/-!
# Completely pinned vacuum prescription

Any ambiguity of the higher packet representation keeping same Wilson
prescription does not change ANY of the coefficients in the next official
RG02 call (on mark and logVac). The paid estimates at a scale are *not*
deduced from this (they must keep the actual reps paid for). But in comparing
the model this ensures no reliance on the choice of basis/renderer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG RG.Supply Pressure Input Org Precision Tree YM.Wilson
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration ThroughLaunch Roost Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Faith QuadraticLocal.Rebirth Comparison.RG02 Comparison.RG02.Bulk
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire AllOrder.Ink AllOrder.Ink.Money
open Laurent Stationary Kinetic.Port Pane Marker Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (R : Run G)
variable {N n i j k m : ℕ}
set_option quotPrecheck false
local notation "sz"=> R.family.side
local notation "S" => R.alloy.B.a.S
local notation "op"=> R.family.path.levels.clock.op
local notation "B" y:max => R.alloy.B.kin.path N y
local notation "cl" x:max=> ( R.alloy.B.a.params x ).clip
local notation "T"=> Step.tape ( k+2 )
variable {π p q : Layout G} {u v:Pace.Coin} {P:PathData G} {b c: Side} {g:Clip}
variable {V:Type}[Fintype V][DecidableEq V]{J: Census V}

section test
variable {S':StepData c b} {Y:ChartRatio G} (A:Bulk.Kernel S' g P Y)
variable {a r δ:ℝ} (h: Forest S'.ratio) (ν:S'.Choices) (X:Bulk.Colors J G b)
variable (hp:Legal (Step.tape (k+2)) p) (hq:Legal (Step.tape (k+2)) q)
variable (he:∀ j:ℕ,j≤ k+2→ Pace.grouping 0 p (Step.tape (k+2)) g P j b=
    Pace.grouping 0 q (Step.tape (k+2)) g P j b)
open PertExtension.Series AllOrder.Laplace Assembly
include hp hq he A
local notation "L" => Link G b
private theorem bass_gap : GradeAt ((k+2)+2+1) (Bulk.projected (QuadraticLocal.Fk.money p T (f:=b) - QuadraticLocal.Fk.money q T)):=by
  obtain ⟨z,u,B',hA⟩:=A.bounds
  let X₀(U:Layout G):= (projected (QuadraticLocal.Fk.money (f:=b) U T))
  let Z:= X₀ p-X₀ q
  change GradeAt _ Z
  let hx:=QuadraticLocal.Fk.level (f:=b) p T hp; let ht:=QuadraticLocal.Fk.level (f:=b) q T hq
  refine ⟨hx.smooth.sub ht.smooth,fun l hl=> ?_⟩
  rw [show Z=X₀ p-X₀ q from rfl,iteratedFDeriv_sub_apply (hx.smooth.of_le le_top) (ht.smooth.of_le le_top)]; apply sub_eq_zero.mpr
  by_cases hy:l<5
  · exact (hx.vanish l hy).trans (ht.vanish l hy).symm
  apply equal_delta hx.smooth ht.smooth
  apply TwoReset.tangent; intro x
  obtain ⟨x,rfl⟩:= (arm G b 1|>.surjective x)
  let e: ℝ×Stationary.Link G b →L[ℝ] ℝ×Exterior.fieldDir G b 1:=
    (ContinuousLinearMap.fst ..).prod ((arm G b 1).toContinuousLinearMap ∘L ContinuousLinearMap.snd ..)
  let u(w:ℝ×L):= primitive (f:=b) P g w.1 (Stationary.input G b w.2)
  have hk: l=l-2+2:= by omega
  have hs' := congr_fun (he (l-2) (by omega)) x
  let Lk:= l-2
  rw [QuadraticLocal.Faith.Costume.genuine P g T p x hp hA, QuadraticLocal.Faith.Costume.genuine P g T q x hq hA, ← hk] at hs'
  have h₀(U:Layout G):Costume.evaluation (n:=b) P g T U = u+(X₀ U ∘ e):=rfl
  rw [h₀,h₀] at hs'
  have hu : ContDiffAt ℝ ω u 0:= by
     let f(b':Stationary.Link G b):=mainTerm g P (Stationary.input G b b')
     let g'(b':Stationary.Link G b):=loop P (Stationary.input G b b')
     change ContDiffAt ℝ ω (fun w:ℝ×Stationary.Link G b=> f w.2+w.1^2*g' w.2) 0
     have hf: ContDiffAt ℝ ω f 0:= (Floe.Pace.intent_point g P hA b|>.analytic.contDiffAt)
     have hg: ContDiffAt ℝ ω g' 0:= (turns_analytic P.loop hA.width hA.two|>.contDiffAt) -- name
     exact (hf.comp (f:=Prod.snd) (0:ℝ×L) contDiffAt_snd).add ((contDiffAt_fst.pow _).mul (hg.comp (f:=Prod.snd) (0:ℝ×L) contDiffAt_snd))
  rw [AllOrder.Laplace.jet_add hu (ContDiffAt.comp _ ((map_zero e).symm ▸ hx.smooth) e.contDiff.contDiffAt),
    AllOrder.Laplace.jet_add hu (ContDiffAt.comp _ ((map_zero e).symm ▸ ht.smooth) e.contDiff.contDiffAt)] at hs'
  replace hs':= add_left_cancel hs'
  unfold PertExtension.Series.Radial.jet at hs'
  rw [Next.Foundations.jets_linear e (hx.smooth.of_le le_top),
    Next.Foundations.jets_linear e (ht.smooth.of_le le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] at hs'
  exact hs'

-- Don't need mark assumptions for logVac stability via any given colors.
local notation "S₁"=> QuadraticLocal.Fk.grant p T X
local notation "S₂"=> QuadraticLocal.Fk.grant q T X
lemma equivalent_calculations {i:ℕ} (hi:i ≤ k+2)(x:Exterior.fieldDir G c 1) :
    Bulk.Fk A h ν (QuadraticLocal.Fk.grant p T X) x i= Bulk.Fk A h ν (QuadraticLocal.Fk.grant q T X) x i := by
  refine same_prescription A h ν (S₁) (S₂) i ?_ (fun i j _ _=>?_ ) x; swap; · change Assembly.markLetter X.power (Bulk.markFn S' h X) _ _ _=Assembly.markLetter X.power (Bulk.markFn S' h X) _ _ _; rfl
  intro j hj x
  unfold vacuumLetter; split
  rfl
  let S1 := S₁; let S2 := S₂
  let f:= Bulk.geometric A h ν (S₁); let g:= Bulk.geometric A h ν (S₂)
  have hf (u:Layout G)(hy:Legal T u): ContDiffAt ℝ ω (Bulk.geometric A h ν (QuadraticLocal.Fk.grant u T X)) 0:= by
      apply (stone_smooth A h ν).add (( ((GradeAt.shifts Prod.fst contDiffAt_fst rfl 2).smooth).mul (officer_known A h).smooth ).add (joint_receipt S' h (QuadraticLocal.Fk.level u T hy)).smooth)
  have hs : f-g = posed S' h (QuadraticLocal.Fk.money p T - QuadraticLocal.Fk.money q T):= by
     ext x; change _+(_+ S1.vac _ _) - (_+(_+ S2.vac _ _))= S1.vac _ _ - S2.vac _ _; abel
  have ht:= (joint_receipt S' h (bass_gap A hp hq he)).vanish (j+2) (by omega)
  rw [← hs, iteratedFDeriv_sub_apply ((hf _ hp).of_le le_top) ((hf _ hq).of_le le_top)] at ht
  apply congr_arg _ (show Assembly.jet f (j+2) x= Assembly.jet g (j+2) x from ?_)
  unfold Assembly.jet; rw [sub_eq_zero.mp ht]
end test

end YM.Integration.FVA1Physical.TwoReset

namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG RG.Supply Pressure Input Org Precision Tree YM.Wilson
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration ThroughLaunch Roost Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Faith QuadraticLocal.Rebirth Comparison.RG02 Comparison.RG02.Bulk
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire AllOrder.Ink AllOrder.Ink.Money
open Laurent Stationary Kinetic.Port Pane Marker Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (R : Run G)
variable {N n i j k m : ℕ}
set_option quotPrecheck false
local notation "sz"=> R.family.side
local notation "S" => R.alloy.B.a.S
local notation "op"=> R.family.path.levels.clock.op
local notation "K" => RunFormalChain.fromRun R
local notation "B" y:max => R.alloy.B.kin.path N y
local notation "cl" x:max=> ( R.alloy.B.a.params x ).clip
local notation "T"=> Step.tape ( k+2 )
variable {π p q : Layout G} {u v:Pace.Coin}
variable {V:Type}[Fintype V][DecidableEq V]{J: Census V}
variable (hi : i < N)
variable (hp:Legal (Step.tape (k+2)) p) (hq:Legal (Step.tape (k+2)) q)

def massJets (R:Run G)(N i k:ℕ)(π:Layout G):= Pace.grouping 0 π (Step.tape (k+2)) ((R.alloy.B.a.params i).clip) (R.alloy.B.kin.path N i)
variable (he:∀ j:ℕ,j≤ k+2→ massJets R N (i+1) k p j= massJets R N (i+1) k q j)
include hp hq he
lemma official_call (A:Forest ((R.family.path.levels.clock.op i n).ratio)) (ν:(op i n).Choices)
    (Y:Bulk.Colors J G (R.family.side (i+1) n)) (x:Stationary.Link G (R.family.side i n)) {j:ℕ} (hj:j≤ k+2) :
    Bulk.Fk ((K).step N i n hi) A ν (QuadraticLocal.Fk.grant p T Y) (arm G (sz i n) 1 x) j=
    Bulk.Fk ((K).step N i n hi) A ν (QuadraticLocal.Fk.grant q T Y) (arm G (sz i n) 1 x) j:= by
  apply equivalent_calculations (hp:=hp) (hq:=hq) (hi:=hj); intro j hj'; rw [(K).clips N n (i+1) hi,(K).selected N n (i+1) hi]; exact congr_fun (he j hj') _

-- mass propagation in the cover prescription uses all suborders and keeps
-- all stencils after projection, not just one finite torus.
lemma mass_same (h: AffineMass R hi p π u k) : AffineMass R hi q π u k:=by
   refine ⟨h.zeroed,h.quote,fun U _ _ J X V M A j hj x=>?_⟩
   have hh (x:Link G X)(z:Covers S i X): coveringVac (k:=k) (y:=j) R hi p J X V M A x z = coveringVac (k:=k) (y:=j) R hi q J X V M A x z:=by
       have he:= official_call R hi hp hq he (M z) (A z) (V z) (convey (coverWin z.prop) x) (le_refl (k+2))
       let π₁ := (coveringDatum R hi p J X V M A k z); let π₂ := (coveringDatum R hi q J X V M A k z)
       let x':= arm G _ 1 (convey (coverWin z.prop) x); let P':=K
       unfold coveringVac; dsimp only
       suffices h: π₁.vacuumAction P' (k+2) j x'=π₂.vacuumAction P' (k+2) j x' from congr_arg (_ • ·) h
       unfold LocalFormal.Datum.vacuumAction Symmetry.Orbit.ground
       exact congr_arg (fun f=> (Order.observe J (k+2) (Order.logVac f) j).part J.quiet+(if j=0 then Symmetry.price ((K).step N i z hi) (M z) (A z) x' else 0)) he
   simp_rw [← hh]; exact h.binding U J X V M A j hj x

-- likewise on paid marks: actual loaded stencils at all preimages
-- use *same* W units. No changing hypotheses on Price.
open QuadraticLocal.Earn QuadraticLocal.Sunrise
lemma enter_same_vac {P : Passport (sz (i+1) n) V} {α ι:Type} (M:ι→ Row P J G α) (w:V→ℕ)
    {Ψ} (hj : j≤ k+2) : MarkCover R hi p T j M w Ψ → MarkCover R hi q T j M w Ψ:=by
  intro h t X hX Y U x l hl; refine (h t X hX Y U x l hl).congr' (Eventually.of_forall (fun z=>?_))
  let C:= copyColor (tiled R hX z) M w (fun i:ι=>(M i).paint t) p T
  have hz:= official_call R hi hp hq he (Y z) (U z) C (convey (coverWin z.prop) x) hj
  exact congr_arg (fun f=> (((Pages X (sz i z.val):ℕ):ℝ)⁻¹ : ℝ) •
    Order.observe J j (Order.logMarked f) l) hz
end YM.Integration.FVA1Physical.TwoReset
