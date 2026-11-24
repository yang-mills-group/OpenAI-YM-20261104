import YM.WilsonCoeffUV.Reclosure.Ordered
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Macrame

/-! Replication of the original periodized Wilson tensor against an arbitrary
full finite test. Relative locations use their original covering windings. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusCopies
open Function Filter Finset Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank
open Matrix RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933
open scoped Classical BigOperators Topology
variable {G:Gauge}{l M:ℕ}{n c:Side}

def seat (n:Side)(a:Site n × (Fin (l+1) → Hooks G))(w:Shift (Keys l)):stars G l n:=
  caseX (fun i=>(a.2 i).2) (fun i=>(a.2 i).1) a.1 w

def pin (X:stars G l n):Site n × (Fin (l+1) → Hooks G):=
  ((X 0).1,fun i=>(X i).2)

private theorem back (a:Site n × (Fin (l+1) → Hooks G))(w:Shift (Keys l)):
    pin (seat n a w)=a:=by
  apply Prod.ext
  · simp [pin,seat,case_head]
  rfl

theorem sections (F:post G l)(H:stars G l n→ℝ)(w:Shift (Keys l)):
    ∑X:stars G l n,H X*flair X F w=
    ∑a:Site n × (Fin (l+1) → Hooks G),
      H (seat n a w) * plantern F (fun i=>(a.2 i).2) (fun i=>(a.2 i).1) w:=by
  classical
  let b:=fun a:Site n × (Fin (l+1) → Hooks G)=>seat n a w
  let f:=fun X:stars G l n=>H X*flair X F w
  have inject:Injective b:=fun a a' eq=>by simpa only [b,back] using congr_arg pin eq
  change ∑X,f X=_
  calc
    _=∑X∈univ.image b,f X:=Eq.symm (sum_subset (subset_univ _) fun X _ out=>by
      have missed:¬trope X w:=by
        intro hit
        apply out
        refine mem_image.mpr ⟨pin X,mem_univ _,?_⟩
        funext i
        apply Prod.ext
        · change (X 0).1+wrap n (feetP w i)=(X i).1
          rw [←hit i]
          abel
        rfl
      simp [f,flair_miss missed])
    _= _:=by
      rw [sum_image inject.injOn]
      exact sum_congr rfl fun a _=>by simp only [f,b,seat,case_flair]

def pull (W:Macrame.Window c n M)(X:stars G l n):stars G l c:=
  fun i=>(W.cut (X i).1,(X i).2)

private theorem sheet (W:Macrame.Window c n M)(u:Site n)(a:Fin (l+1) → Hooks G)
    (w:Shift (Keys l)):pull W (seat n (u,a) w)=seat c (W.cut u,a) w:=by
  funext i
  apply Prod.ext
  · change W.cut (u+wrap n (feetP w i))=W.cut u+wrap c (feetP w i)
    rw [add_comm u,W.rooted,add_comm]
  rfl

theorem winding (F:post G l)(W:Macrame.Window c n M)(H:stars G l c→ℝ)(w:Shift (Keys l)):
    ∑X:stars G l n,H (pull W X)*flair X F w=M • ∑X:stars G l c,H X*flair X F w:=by
  rw [sections F (fun X=>H (pull W X)) w,sections F H w]
  simp only [Fintype.sum_prod_type,sheet]
  exact Shingle.multiplied W.cut W.fold (fun u:Site c=>∑a:Fin (l+1) → Hooks G,
    H (seat c (u,a) w)*plantern F (fun i=>(a i).2) (fun i=>(a i).1) w)

def total (F:post G l)(n:Side)(H:stars G l n→ℝ):ℝ:=
  ∑X,H X*lagoon F n X

theorem original (F:post G l){s A:ℝ}(paid:Amber terrain s A F)(width:0<s)
    (W:Macrame.Window c n M)(H:stars G l c→ℝ):
    total F n (H ∘ pull W)=M • total F c H:=by
  have joined (n:Side)(Z:stars G l n→ℝ):total F n Z=∑'w,∑X:stars G l n,Z X*flair X F w:=by
    have enough (X:stars G l n):Summable fun w=>Z X*flair X F w:=
      ((flair_cost paid width X).summable (hinge_paid width _).le).mul_left (Z X)
    unfold total lagoon
    simp only [←tsum_mul_left]
    exact Summable.tsum_finsetSum (fun X _=>enough X) |>.symm
  rw [joined,joined]
  simp only [Function.comp_apply,winding,nsmul_eq_mul,tsum_mul_left]
  
def repeated (W:Macrame.Window c n M)(z:Co c (Hooks G) → ℝ)(v:Co n (Hooks G)):ℝ:=
  z (W.cut v.1,v.2)

theorem painted (F:post G l){s A:ℝ}(paid:Amber terrain s A F)(width:0<s)
    (W:Macrame.Window c n M)(z:Co c (Hooks G) → ℝ):
    MvPolynomial.eval (repeated W z) (Blue.paint (l+1) (lagoon F n))=
      M • MvPolynomial.eval z (Blue.paint (l+1) (lagoon F c)):=by
  have scalar (n:Side)(v:Co n (Hooks G) → ℝ):
      MvPolynomial.eval v (Blue.paint (l+1) (lagoon F n))=
        total F n (fun X=>∏i,v (X i)):=by
    change MvPolynomial.eval v (∑X,lagoon F n X • ∏i,MvPolynomial.X (X i))=_
    simp [total,MvPolynomial.smul_eq_C_mul,mul_comm]
  rw [scalar,scalar]
  exact original F paid width W (fun X=>∏i,z (X i))

end YM.Integration.WilsonVacuumPreResetTorusCopies
