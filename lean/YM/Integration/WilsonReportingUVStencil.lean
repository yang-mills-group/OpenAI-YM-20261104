import YM.Integration.WilsonReportingUVProbe

/-! The actual ultraviolet site weights of a displaced Wilson singleton.
The signed linear rule retains the exact integer child anchor at every
stage and can be evaluated on any field of the microscopic sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUVStencil
open Function Set Finset MeasureTheory Lattice Wilson RG Source RG05Readout Native Address Many Records
open Extra.Histories PhysicalNext.Repeat.Legato WilsonReportingUVCell WilsonReportingUVReturn
open WilsonPositionSeparatedProfileCenteredBranch
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N p:ℕ)

abbrev Rule (n:Side):=(Site n→ℂ)→ₗ[ℂ]ℂ
def atSite {n:Side} (z:Site n):Rule n:=LinearMap.proj z
def slide {n:Side} (a:Site n):(Site n→ℂ)→ₗ[ℂ](Site n→ℂ):=
  LinearMap.pi (fun z=>atSite (z+a))

def evaluate {n:Side} (X:Goods G n) (U:Config G n) (z:Site n):ℂ:=X (pull 1 z U)

theorem shifted {n:Side} (X:Goods G n) (U:Config G n) (a:Site n) :
    evaluate X (pull 1 a U)=slide a (evaluate X U):=by
  funext z
  change X (pull 1 z (pull 1 a U))=X (pull 1 (z+a) U)
  apply congrArg X
  simp only [pull_one]
  funext e
  simp only [Lattice.translate,add_assoc]

def read {n:Side} (A:Body→Rule n) (X:Goods G n) : Bin G n:=fun φ U=>A φ (evaluate X U)

def copy (d:ℕ) {j:ℕ} (top:j+1≤N) (A:Body→Rule (R.family.side N p)) (φ:Body):Rule (R.family.side N p):=
  ((R.family.S.block j).val:ℂ)^d • Address.average (fun s:Bud R.family p j=>
    (A (headFee R.family p j s φ)).comp (slide (Push.GridApprox.anchor R.family.S p top (child R.family p j s))))

theorem step (d:ℕ) {j:ℕ} (top:j+1≤N) (A:Body→Rule (R.family.side N p))
    (X:Goods G (R.family.side N p)) :
    merged R N p d top (read A X)=read (copy R N p d top A) X := by
  funext φ U
  simp only [merged,read,copy,Address.average,Pi.smul_apply,Finset.sum_apply,
    LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul,arrangement,Function.comp_apply,LinearMap.comp_apply,
    shifted]

def archive (m d:ℕ):(q:ℕ)→m+q ≤ N→(Body→Rule (R.family.side N p))→Body→Rule (R.family.side N p)
  | 0,_,A=>A
  | q+1,live,A=>archive m d q (by omega) (copy R N p d live A)

theorem history (m d q:ℕ) (top:m+q≤N) (A:Body→Rule (R.family.side N p)) (X:Goods G (R.family.side N p)) :
    sheets R N p m d q top (read A X)=read (archive R N p m d q top A) X := by
  induction q generalizing A with
  | zero=>rfl
  | succ q ih=>
    change sheets R N p m d q _ (merged R N p d top (read A X))=read (archive R N p m d q _ _) X
    rw [step]
    exact ih (by omega) _

def seed {d:ℕ} (t:Letter d) (φ:Body):Rule (R.family.side N p):=
  (readJ t 0 φ*(R.family.S.a N:ℂ)^kept t) • atSite 0

def weights {m d:ℕ} (t:Letter d) (live:m ≤ N) (φ:Body):Rule (R.family.side N p):=
  archive R N p m d (N-m) (by omega) (seed R N p t) φ

theorem microscopic {m d:ℕ} (t:Letter d) (x:R.family.label (kept t)) (live:m≤N) (φ:Body)
    (U:Config G (R.family.side N p)):
    WilsonReportingUVLikelihood.observable R N p t x live φ U=
      weights R N p t live φ (evaluate (R.family.O N p x 0) U) := by
  have base:WilsonReportingUVReturn.raw R N p t x=read (seed R N p t) (R.family.O N p x 0):=by
    funext ψ A
    change _= _*(R.family.O N p x 0 (pull 1 0 A))
    rw [pull_one,show Lattice.translate 0 A=A from by funext e; simp [Lattice.translate]]
    rfl
  change sheets R N p m d (N-m) _ (WilsonReportingUVReturn.raw R N p t x) φ U=_
  rw [base]
  exact congrFun (congrFun (history R N p m d (N-m) (by omega) (seed R N p t) (R.family.O N p x 0)) φ) U

end YM.Integration.WilsonReportingUVStencil
