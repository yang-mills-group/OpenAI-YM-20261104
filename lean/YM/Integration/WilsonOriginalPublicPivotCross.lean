import YM.Integration.WilsonOriginalPublicPivotFaces

/-! The two one-residual ears of the measured primitive are ordinary finite
Gaussian readings at the true reflected positions, on the same tested film
as its full physical self-reading and finite fitted Gram. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 550000
namespace YM.Integration.WilsonOriginalPublicPivotCross
open Finset Function PowerSeries Lattice RG Wilson Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open Source MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicWickGram (nodes reading)
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicPivotReflected (sampled evaluated board)
open WilsonOriginalPublicPivotFaces (tests earlier raw)
open WilsonPositionProgramTrialThermalGrades (frozen)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){L I:Type} [Fintype L] [Fintype I]

abbrev Film {G:Gauge} (W:Initialize G) := (x:Sample 2)→ Bare.Series (W.tree x.F.p) G

def detector (X:L→Sample 2)(μ:L→ℂ)(q:ℕ)(g:ℝ): Film W →ₗ[ℂ] ℂ:=
  let cash:=∑k∈Finset.Iic q,(g:ℂ)^k • coeff (R:=ℂ) k
  ∑l,μ l • (cash ∘ₗ Bare.normalized (W.tree (X l).F.p) G ∘ₗ LinearMap.proj (X l))

variable (h:Fin 2→ℕ)(v:(i:Fin 2)→(R.family.labels.level (h i)).Coeff)
    (X:L→Sample 2)(μ:L→ℂ)(q:ℕ)(g:ℝ)
def col (i:Fin 2):Film W :=fun x=>raw R W h v x i
def old:ℂ:=tests X μ q g (fun x=>earlier R W h v x univ)

theorem source:sampled R W h v X μ univ q g=
    old R W h v X μ q g + detector W X μ q g (col R W h v 0 * col R W h v 1):=by
  have line(l:L):board R W h v (X l) univ=earlier R W h v (X l) univ+
      Bare.normalized (W.tree (X l).F.p) G (col R W h v 0 (X l)*col R W h v 1 (X l)):=by
    let S:Finset (Fin 2):=univ
    let d:S→ℕ:=h ∘ Subtype.val
    have f:=WilsonThermometerPositionTunedCorrection.earned R W d (X l).F.p
      (fun i:S=>(X l).layout i) (W.tree (X l).F.p) (frozen R d (fun i:S=>v i))
    rw [WilsonOriginalPublicFigureWickFaces.folded R W h v (X l) S] at f
    have full : board R W h v (X l) S=earlier R W h v (X l) S+
        Bare.normalized (W.tree (X l).F.p) G (∏i∈S,col R W h v i (X l)):=sub_eq_iff_eq_add.mp f
    simpa only [S,Fin.prod_univ_two] using full
  simp only [sampled,old,WilsonOriginalPublicPivotFaces.tests,line,evaluated,detector,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,LinearMap.proj_apply,Pi.mul_apply,smul_eq_mul,map_add,mul_add,sum_add_distrib]

variable (a:I→ℂ)(A B:I→Film W)
def left : Film W := col R W h v 0 - ∑i,star (a i) • A i
def right : Film W := col R W h v 1 - ∑i,a i • B i
local notation "H" => detector W X μ q g
local notation "U" => left R W h v a A
local notation "V" => right R W h v a B

theorem spread:sampled R W h v X μ univ q g=
    assay a a (fun i j=>H (A i*B j))+
    ((∑i,star (a i)*H (A i*V))+(∑i,a i*H (U*B i)))+
    (old R W h v X μ q g+H (U*V)):=by
  have l:col R W h v 0=(∑i,star (a i) • A i)+U:=by unfold left;abel
  have r:col R W h v 1=(∑i,a i • B i)+V:=by unfold right;abel
  have one:H ((∑i,star (a i) • A i)*V)=∑i,star (a i)*H (A i*V):=by
    rw [sum_mul,map_sum]
    simp only [smul_mul_assoc,map_smul,smul_eq_mul]
  have two:H (U*(∑i,a i • B i))=∑i,a i*H (U*B i):=by
    rw [mul_sum,map_sum]
    simp only [mul_smul_comm,map_smul,smul_eq_mul]
  have main:H ((∑i,star (a i) • A i)*(∑i,a i • B i))=assay a a (fun i j=>H (A i*B j)):=by
    rw [sum_mul,map_sum]
    unfold assay
    refine sum_congr rfl (fun i _=>?_);rw [mul_sum,map_sum]
    refine sum_congr rfl (fun j _=>?_)
    simp only [smul_mul_assoc,mul_smul_comm,map_smul,smul_eq_mul]
    ring
  rw [source,l,r,add_mul,mul_add,mul_add,map_add,map_add,map_add,one,two,main]
  abel

private theorem charge {x y:I→ℂ}{M b:ℝ}(xb:∀i,‖x i‖≤b)(bp:0≤b)
    (yp:∑i,‖y i‖≤M):
    ‖∑i,x i*y i‖≤M*b:=by
  calc
    _ ≤ ∑i,‖x i*y i‖:=norm_sum_le ..
    _ ≤ ∑i,b*‖y i‖:=sum_le_sum fun i _=>by rw [norm_mul];gcongr;exact xb i
    _ ≤ _:=by rw [←mul_sum,mul_comm];exact mul_le_mul_of_nonneg_right yp bp

theorem difference {e u t:ℝ}
    (first:∑i,‖H (A i*V)‖≤e*u)(second:∑i,‖H (U*B i)‖≤e*u)
    (both:‖old R W h v X μ q g+H (U*V)‖≤e*u^2+t):
    ‖assay a a (fun i j=>H (A i*B j))-sampled R W h v X μ univ q g‖≤e*(2*u*‖a‖+u^2)+t:=by
  have eq:sampled R W h v X μ univ q g-assay a a (fun i j=>H (A i*B j))=
      ((∑i,star (a i)*H (A i*V))+(∑i,a i*H (U*B i)))+
      (old R W h v X μ q g+H (U*V)):=by rw [spread R W h v X μ q g a A B];abel
  rw [norm_sub_rev,eq]
  have lh:=charge (x:=fun i=>star (a i)) (b:=‖a‖)
    (fun i=>by simpa only [norm_star] using (norm_le_pi_norm a i)) (norm_nonneg _) first
  have rh:=charge (x:=a) (b:=‖a‖) (fun i=>norm_le_pi_norm a i) (norm_nonneg _) second
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add lh rh)) both).trans_eq (by ring))

end YM.Integration.WilsonOriginalPublicPivotCross
end
