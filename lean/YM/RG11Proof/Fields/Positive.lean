import YM.RG11Proof.Fields.Coordinates
import YM.RG11Proof.Bridge.Leading
import YM.PertExtension.ReflectFrame

/-!
# Supply the finite-order Gram detector on the actual *free physical* quotient

At every fixed finite horizon obtain ONE complex compact smooth test with real
parts of Wick two-point readings giving a matrix positive definite after fixed
index reflection. No claim of actual regulator positivity, lower bounds on actual
Gram, or branch compatibility beyond the free field space. Need the common
finite basis/rank choice and exact rates for this selected test before feeding
those outputs to `Bridge.leading_of_paired` (and `R` should be grade-compatible
with the chosen induction order; dealt with separately). -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets Function Set Labels Maxwell YM.Pert.Position Extra.FD
open scoped Classical BigOperators ComplexOrder
variable {G:Gauge} {F:Frames G} {d:ℕ} (B:Basis F d)

private def pt (x y:E4) : Points 2 := Extra.FD.couple x y
private def pos (a:Axis) : Points 2 := pt (_root_.YM.basis a) 0
private theorem parted (a:Axis): pos a∈conf 2:= by
  apply Extra.FD.couple_ok; intro h; simpa [YM.basis_norm] using! congrArg norm h

/-- Reflection REMNANT for disposition in second index, so use real basis
and take real parts on the regulator and pivot arrays on this test. -/
def frameMirror (a:Axis): Square B.J ℝ:= Matrix.of fun i j=>B.coord ((freeTable F).adj (table_spin F) d a (B.b i)) j

theorem mirror_put (a:Axis)(i:B.J):B.put (fun j=>frameMirror B a i j)=(freeTable F).adj (table_spin F) d a (B.b i):=by
  apply B.put_round
  unfold Basis.overReals Table.adj
  simp only [LinearMap.comp_apply,B.pinned,Table.mirror_star]

def freeTwo (x:Points 2)(i j:B.J):ℝ:= (visible F d x ![B.b i,B.b j]).re

local notation "Gram"=>YM.PertExtension.Rigidity.Positive.gram
local notation "sourceGram"=>YM.PertExtension.Rigidity.Positive.gramC

theorem pair_gram (H:(freeTable F).Hierarchy) (a:Axis) (i j:B.J):
    Gram F H a (B.b j) (B.b i) = Bridge.gramAt (Matrix.of (freeTwo B (pos a))) (frameMirror B a) i j:=by
  change (sourceGram F H a (B.b j) (B.b i)).re = _
  rw [YM.PertExtension.Rigidity.Positive.gramC_apply]
  have hv (x y:E F d) : (freeTable F).useAt (freeTable F) (pos a) ![⟨d,x⟩,⟨d,y⟩]=visible F d (pos a) ![x,y]:= by
    have ht : visible F d (pos a) ![x,y] = (freeTable F).useAt (freeTable F) (pos a)
          (fun i=> (Sigma.mk d (![x,y] i):(freeTable F).Tag)):=rfl
    rw [ht]
    apply congrArg ((freeTable F).useAt (freeTable F) (pos a)); funext l; fin_cases l <;> rfl
  change ((freeTable F).useAt (freeTable F) (pos a) _).re = _
  rw [hv (B.b i) (show E F d from (freeTable F).adj (table_spin F) d a (B.b j))]
  rw [← mirror_put _ _ j, Basis.put_sum]
  let M:= visible F d (pos a)
  let L:= M.toLinearMap (![B.b i,(0:E F d)]) 1
  have he(y:E F d): M ![B.b i,y]=L y:= by
    rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 r; fin_cases r <;> simp
  unfold Bridge.gramAt freeTwo
  change (M _).re=∑ l,frameMirror B a j l*(M ![B.b i,B.b l]).re
  simp_rw [he,map_sum,map_smul,smul_eq_mul,Complex.re_sum,Complex.re_ofReal_mul]

-- Need Hierarchy: baseline theorem? #check
-- `parted` avoids any coincidence constraint (and exactTest is conf).
theorem positive_basis (H:(freeTable F).Hierarchy)(a:Axis) :
    Bridge.Positive (Matrix.of (freeTwo B (pos a))) (frameMirror B a) := by
  intro x hx
  have he:=B.put_injective.ne (a₁:=x) hx
  rw [Basis.put_zero] at he
  have hp : 0<(sourceGram F H a (B.put x) (B.put x)).re :=
    (Complex.lt_def.mp (YM.PertExtension.Rigidity.Positive.gramC_pos F H a he)).1
  change 0 < Gram F H a (B.put x) (B.put x) at hp
  have hx' : B.put x = ∑ j,x j • B.b j := by
    rw [Basis.put_sum]; apply Finset.sum_congr rfl; intro j _; exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (x j) _).symm
  rw [hx',map_sum] at hp
  simp only [map_sum, LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,pair_gram] at hp
  convert hp using 1
  simp only [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>by ring

/-- Smooth single-test real-valued pair matrix. Combine real/imag by supplying
this complex profile on every finite mark. The matrix formula and reflection
use the baseline leading Wick kernel, not the interacting points. -/
def freePair (f : YM.Test 2) : Square B.J ℝ:= Matrix.of fun i j=>(wickReading F d f ![B.b i,B.b j]).re

theorem positive_profile (H:(freeTable F).Hierarchy) (a:Axis) : ∃ f : YM.Test 2,
    Bridge.Positive (freePair B f) (frameMirror B a):=by
   obtain ⟨f,hf⟩ := exactTest (parted a) (fun (z:B.J × B.J) x=>visible F d x ![B.b z.1,B.b z.2]) (fun z=>visible_cont F d _)
   refine ⟨f,?_⟩
   rw [show freePair B f=Matrix.of (freeTwo B (pos a)) from Matrix.ext (fun i j=>congrArg Complex.re (hf (i,j)))]
   exact positive_basis B H a
end YM.RG11.Fields
