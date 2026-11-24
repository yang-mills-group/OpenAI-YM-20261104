import YM.Integration.WilsonVacuumPreResetJointRouted
import YM.Integration.WilsonCubicSummedLocalPolynomial
import YM.Integration.WilsonRootedCubicPathCut

/-! The independent tensor at one actual occupied root, orientation and
registered path family, before any spatial sum or normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointRootReading
open WilsonCoeffUV
open Filter Function Finset Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Power Stationary AnalyticNext.QuarticMatch.Estimate Near
open Work.G05 WilsonCubicLocalPolynomial WilsonCubicSummedLocalPolynomial
open Tree Pressure Pressure.Stores Pressure.Tube Push Push.Uniform Push.AbsoluteSums ConnectedActivityE6 SliceRows Coat Matter Blaze RG01.Sounder
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw WilsonLimitConstruction Analysis
open private sum_green add_rows from YM.Integration.WilsonCubicSummedLocalPolynomial
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {k : ℕ} {σ C : ℝ}

def tensor (A:ℕ→Atom G k)(l:Signed)(x:Site f)(n:ℕ)(v:Fin n→Woods G f):ℝ:=
  ∑'i:ℕ,rye (reader A (l,x,i)) n v

def polynomial (A:ℕ→Atom G k)(l:Signed)(x:Site f)(d:ℕ)(u:Link G f):ℝ:=
  ∑n∈range (d+1),MvPolynomial.eval u (paint n (tensor A l x n))

theorem paid (A:ℕ→Atom G k)(hs:0<σ)(cash:SumBudget (fun i=>(A i).budget σ) C)
    (l:Signed)(x:Site f)(n:ℕ):
    tensor A l x n=rye (site A l x) n:=by
  funext v
  exact (local_sum A hs cash l x v).tsum_eq

theorem genuine (A:ℕ→Atom G k)(l:Signed)(x:Site f)(u:Link G f):
    (∑'i:ℕ,(A i).unmasked (pull l 0 (Stationary.input G f u)) x)=site A l x u:=by
  change (∑'i:ℕ,reader A (l,x,i) u)=_
  have h (i:ℕ):reader A (l,x,i)=Cargo.effect (A i) x ∘ orbit G f l:=issued A (l,x,i)
  simp_rw [h]
  rfl

theorem printed (A:ℕ→Atom G k)(hs:0<σ)(cash:SumBudget (fun i=>(A i).budget σ) C)
    (l:Signed)(x:Site f)(d:ℕ):
    polynomial A l x d=blockTaylor d (site A l x):=by
  funext u
  unfold polynomial blockTaylor
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [paid A hs cash,←jet_apply]
  exact rayon _ _ _

theorem enrolled (a:PrismA G)(hs:0<σ)(bank:Commission a.cells σ C a.grade)(n:ℕ)(v:Fin n→Woods G f):
    Mosaic.surf a f (WilsonVacuumPreResetJointPublished.lag a n) n v=
      Patch.average fun l:Signed=>∑x:Site f,tensor a.cells l x n v:=by
  have each (l:Signed)(x:Site f):Green (site a.cells l x):=
    (Village.atend_rate a.cells hs bank.toll x _).comp _ (orbit G f l).contDiff.contDiffAt
  have all (l:Signed):=sum_green _ (each l)
  have whole:=sum_green _ all
  have written:turnSeries a.cells (m:=f)=(Fintype.card Signed:ℝ)⁻¹ • (∑l:Signed,∑x:Site f,site a.cells l x):=by
    funext u
    rw [turns_frame]
    simp only [Patch.average,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
    rfl
  rw [WilsonVacuumPreResetJointPublished.rank a hs bank n,written,rye_mu _ _ whole,add_rows _ all]
  simp only [Patch.average,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  apply congrArg ((Fintype.card Signed:ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro l _
  rw [add_rows _ (each l),Finset.sum_apply]
  exact Finset.sum_congr rfl fun x _=>congrFun (paid a.cells hs bank.toll l x n).symm v

theorem logarithm (v:Directions G f):
    Stationary.input G f (WilsonCubicOriginalTorus.coordinates G f v)=RG.increment 1 v:=by
  change represent (arm G f 1 ((arm G f 1).symm (toLog v)))=_
  rw [ContinuousLinearEquiv.apply_symm_apply,edits]

theorem seated (W:book G k)(l:Signed)(x:Site f)(X:Coat T F)(p:Molecule S)(kept:p.toLeft=∅)
    (sun:flags (Pressure.temp X.x) X.V=∅)(Y:F.Slice G)(d:ℕ):
    let Z:=(Matter.planted X p).wrapY Y
    let u:=WilsonCubicOriginalTorus.coordinates G f ∘ changes univ Z
    blockTaylor d (W.slab l x ∘ field univ Z)=
      blockTaylor d (polynomial W.words l x d ∘ blockTaylor d u):=by
  intro Z u
  let v:=site W.words l x
  have at0:field univ Z 0=1:=WilsonVacuumPreResetJointBranch.base X p kept sun Y
  have agree:W.slab l x ∘ field univ Z =ᶠ[𝓝 0] v ∘ u:=by
    filter_upwards [agrees univ Z] with w hw
    change W.slab l x (field univ Z w)=site W.words l x (u w)
    rw [hw,at0,←logarithm,←genuine]
    rfl
  have zero:u 0=0:=by simp [u,changes_zero]
  have ht:ContDiffAt ℝ d u 0:=(WilsonCubicOriginalTorus.coordinates G f).contDiff.contDiffAt.comp _
    ((smooth univ Z).of_le le_top)
  have hv:ContDiffAt ℝ d v 0:=((Village.atend_rate W.words W.pos W.fee x _).comp _
    (orbit G f l).contDiff.contDiffAt).of_le le_top
  have z0:blockTaylor d u 0=0:=(blockTaylor_zero d u).trans zero
  have eq:=jets_comp (x:=0) (g:=v) (g':=blockTaylor d v) ht (blockTaylor_contDiff d u _).contDiffAt
    (zero.symm ▸ hv) (blockTaylor_contDiff d v _).contDiffAt (zero.trans z0.symm)
    (fun n hn=>(blockTaylor_jets ht n hn).symm)
    (fun n hn=>by rw [z0];exact (blockTaylor_jets hv n hn).symm)
  rw [printed W.words W.pos W.fee l x]
  unfold blockTaylor
  apply Finset.sum_congr rfl
  intro n hn
  have join:=((agree.iteratedFDeriv ℝ n).eq_of_nhds).trans (eq n (by simpa using hn))
  simp only [Tensor.coeff,join]
  rfl

end YM.Integration.WilsonVacuumPreResetJointRootReading
