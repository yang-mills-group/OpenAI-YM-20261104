import YM.Integration.WilsonMovingForkPositionIntegrals

/-! The independent two-group programme as a predicate of the one
physical position tuple consumed at each actual screened node. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkPointPrescription
open Spec Lattice Wilson RG Source RG17 Extraction Table XSpace XSpace.Normalize Maxwell
open Climb FVA2 FVA2.Register FVA2.O FVA2.O.Project FVA2.O.Score FVA2.Scale FVA2.O.Enh
open MS MS.Land MS.Fleet MS.Theater
open WilsonMovingForkCanonicalKernels WilsonMovingForkKernelIntegrals
open WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open scoped Classical BigOperators
variable {G:Gauge}(C:Family G){n:ℕ}(d:Fin n → ℕ)(h:ℕ)(Z:WilsonPrescription G)
def inside (r:ℝ)(x:Points (n+1)):Points n:=points fun i=>r⁻¹ • x (Fin.castAdd 1 i)
def outside (t:ℝ)(x:Points (n+1)):Points 2:=
  points (Fin.cons (0:E4) (fun j:Fin 1=>t⁻¹ • x (Fin.natAdd n j)))

def many (q:ℕ)(g s r t:ℝ)(v:∀i,Free C (d i))(a:Free C h)(x:Points (n+1)):ℂ:=
  fullAt C d h Z q g s v a (inside r x,outside t x)
def two (q:ℕ)(g s t:ℝ)(a:Free C h)(k:Dframe.Toon G h)(x:Points 2):ℂ:=
  gramAt C h Z q g s a k (t⁻¹ • x)

theorem whole (q:ℕ)(g s r t:ℝ)(rp:0<r)(tp:0<t)(v:∀i,Free C (d i))(a:Free C h)
    (u:Points n)(z:Points 2):
    many C d h Z q g s r t v a (placed r t u (relative z))=fullAt C d h Z q g s v a (u,z):=by
  have left:inside r (placed r t u (relative z))=u:=by
    ext1 i
    change r⁻¹ • Fin.append (fun k=>r•u k) (fun k=>t•relative z k) (Fin.castAdd 1 i)=u i
    rw [Fin.append_left,inv_smul_smul₀ rp.ne']
  have right:relative (outside t (placed r t u (relative z)))=relative z:=by
    ext1 i
    change t⁻¹ • Fin.append (fun k=>r•u k) (fun k=>t•relative z k) (Fin.natAdd n i)-(0:E4)=_
    rw [Fin.append_right,inv_smul_smul₀ tp.ne',sub_zero]
  simp only [many,fullAt,WilsonMovingForkCanonicalKernels.many,left,right]

theorem gram (q:ℕ)(g s t:ℝ)(tp:0<t)(a:Free C h)(k:Dframe.Toon G h)(x:Points 2):
    two C h Z q g s t a k (t • x)=gramAt C h Z q g s a k x:=by
  unfold two
  rw [inv_smul_smul₀ tp.ne']

end YM.Integration.WilsonMovingForkPointPrescription
