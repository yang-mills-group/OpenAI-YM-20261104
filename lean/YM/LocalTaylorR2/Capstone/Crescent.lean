import YM.LocalTaylorR2.Capstone.Lens
/-!
 # Regular Taylor and error on same `Drawer` addresses through finish/Widen

 Costs no support inflation on final E. Final K immutable, taken as part of
 the exceptional system -- NOT forming a cheaper model by deleting it or
 encoding its payload in a representation indistinguishable by vacuum.
 Precise norm after combining through projection. Includes genuine operator formula
 at Rep.eval (with actual β/path/clip/scalar SEPARATE from this main/error in E --
 kinetic/scalar error estimate per site treated elsewhere actual path).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Capstone
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6
open MeasureTheory ProbabilityTheory
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Input Org Supply Slide Marlin Trio Height Opera Boulevard Testing
open Push.PriceCompiler
open Progress.DirectedRecipe Rack Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
section barrel
variable {G:Gauge}{n:Side} {P:BudgetPoint} (Z:Pipes G n) (d: Tap G n) (A:Activities G n) (R:Rep G n)
    {e u w f a y : ℝ} {δ κ : Tap G n} (h : (Z.pours d).EBound P e)
def drawn : ℕ → Config G n→ℝ:= stuff (upE Z) d.regular
-- don't mutate even blanks not yet used
lemma trace_widens (hz:(Z.pours d).RegularFamily P):
    let V:={(drawer G n).pours (widen Z d) with forced := A.forced, K := A.K}
    V.E=drawn Z d ∧ V.RegularFamily P:=by
  intro V; have hF:= (preserves Z d P).regular hz; exact ⟨rfl,hF.smooth,hF.at_flat,hF.vanish⟩
def varyP : Activities G n:= { A with E:= drawn Z d }
lemma moveUp (hp : A.reg=(drawer G n).reg)(hv : A.Valid P w a)(hq : (Z.pours d).Valid P e y) :
    (varyP Z d A).Valid P e a:=by
   have he:= (preserves Z d P).Ebound hq.boundE
   have hF:= (preserves Z d P).regular hq.regular
   have hH:=hv.forced
   have hR:(varyP Z d A).RegularFamily P:=by unfold varyP; rw [hp]; exact ⟨hF.smooth,hF.at_flat,hF.vanish⟩
   refine ⟨hR,⟨hH.sym,hH.symtest,hH.meas,hH.meas_test,hH.reads,hH.reads_test,hH.permit⟩,fun i j=>?_,?_,hv.boundK⟩
   · let u:= on_shelves (hq.moves i j|>.some)
     let D:= hv.moves i j|>.some
     unfold varyP; rw [hp]; exact ⟨⟨u.ep,D.kp,u.reg_site,u.reg_support,D.forced_support,D.forced_inventory,D.forced_tests,u.valuesE,D.valuesK⟩⟩
   unfold varyP; rw [hp]; exact he
lemma pouring_reg (hf : d.regular - δ.regular = κ.regular): drawn Z d= drawn Z δ + drawn Z κ:= by
  ext1 i; by_cases he:i∈Set.range (upE Z)
  · obtain ⟨j,rfl⟩:=he; unfold drawn; rw [Pi.add_apply,stuffed,stuffed,stuffed]; rw [eq_add_of_sub_eq' hf]; rfl
  unfold drawn; rw [Pi.add_apply,blank _ _ he,blank _ _ he,blank _ _ he]; simp
lemma tollsUp (hp : R.p=P) (_hK:R.activities.reg=(drawer G n).reg)(hx: R.activities.E= drawn Z d)(hF : d.regular - δ.regular=κ.regular)
    (h : (varyP Z δ R.activities).Valid P e f)(hr:(varyP Z κ R.activities).Valid P w a):
    let U:Rep G n:={R with activities:= varyP Z δ R.activities}
    let V:=varyP Z κ R.activities
    R.eval= U.eval*fun X=> Real.exp (-(V.additive P X)):=by
  intro U V
  have he:= Eq.trans hx (pouring_reg Z d hF)
  have hn X: R.activities.additive P X=U.activities.additive P X+V.additive P X:= by
    unfold Activities.additive
    rw [← Summable.tsum_add ((Activities.ESeries h).summable X) ((Activities.ESeries hr).summable X)]
    refine tsum_congr fun i=>?_
    let j:=R.activities.reg i; let F:=R.activities.E i
    unfold Activities.regularOccurrence; rw [he]; dsimp only [varyP]
    by_cases h : Healthy P.threshold j.support X
    · rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ h, masked_eq _ _ _ _ h]; rfl
    rw [masked_ne _ _ _ _ h, masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,add_zero]
  have hk : R.activities.gas P=U.activities.gas P:= rfl
  ext1 X
  unfold Rep.eval Rep.exponent; simp only [Pi.mul_apply]; change _=(Real.exp (R.v*Fintype.card (Site n)-R.path.inChannels R.clip R.p R.beta X-U.activities.additive R.p X)*U.activities.gas R.p X)*Real.exp (-(V.additive P X)) -- clip? path structures
  rw [hp,hk,hn,mul_right_comm _ (U.activities.gas P X),← Real.exp_add]; ring_nf -- check
lemma sleepers (hp : HasSlots P A) : HasSlots P (varyP Z d A):= ⟨hp.reg,hp.forced,fun i=> blank _ _ (distinct _ _ i.1 i.2),hp.forced_zero⟩
end barrel
end YM.LocalTaylorR2.Capstone
