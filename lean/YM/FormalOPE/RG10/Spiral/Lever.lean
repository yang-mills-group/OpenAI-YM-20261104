import YM.FormalOPE.RG10.Spiral.Rig

/-!
# Wick rule on the linear quotient of **periodic** token polynomials

Values only on periodic full-torus linear curls are needed,
not extra identities on unconstrained input planes. Pre-period-removal. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Spiral
open Function Wilson Lattice Gauge Precision Exterior Work.F03 Further.CorrectedLift.Compass
   PertExtension Filter RG PertExtension.LatticePT LatticePT.Projection Finset
open Next.Rank Hue Normal MvPolynomial
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge} {n : Side}
local notation "Λ" => Hue.Panel RG.Slot G
local notation "ν" => LatticePT.colorBasis (G:=G)
local notation "L" => Hue.Panel (FaceAt n) G
local notation "γ" => Bid.Dir G n
abbrev fold (a:L) :γ:= tap a.1 (ν a.2)
abbrev paid (a b:L) := earning a.1 b.1 (ν a.2) (ν b.2)
abbrev see (b:Λ) : L := (Converter.position n b.1,b.2)
lemma paid_eq (a b:L): paid a b = Spiral.tone a (fold b):= EuclideanSpace.basisFun_inner ..
lemma coin (a b:L) : ∑ p : L, paid a p * paid b p=paid a b := by
 rw [show paid a b = _ from (earned a.1 b.1 (ν a.2) (ν b.2)).symm]; -- which rewrites?
 apply Finset.sum_congr rfl; intro i _
 have hp a b : paid (G:=G) (n:=n) a b= paid b a:= earning_comm ..
 rw [hp a i,hp b i,paid_eq,paid_eq]
lemma expense (a:L) (v:γ) : ∑ p : L, paid a p * Spiral.tone p v= Spiral.tone a v := by
  have he := pays a.1 (ν a.2) v; rw [LatticePT.colorBasis,EuclideanSpace.basisFun_inner] at he; change _= (faceCurl a.1 v) a.2; rw [← he]; unfold overlap
  rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [PiLp.inner_apply]; apply sum_congr rfl; intro j _
  rw [show paid a (i,j)=_ from (earning_comm a.1 i (ν a.2) (ν j)).trans (paid_eq (i,j) a),mul_comm]; rfl
variable (n) in
def lever (v:Λ) : L →₀ ℂ := ∑ i:L, Finsupp.single i (Complex.ofReal (paid (see v) i))
variable (L':Type*) in
def diagonal : Symmetric L' := ⟨fun i j=>if i=j then 1 else 0, fun i j=>by simp_rw [eq_comm]⟩ -- loops?
lemma loft : scope (lever n) (diagonal L)=rig (G:=G) n := by
 apply Normal.Symmetric.ext; funext i j
 change treats _ _ _=(Complex.ofReal _); unfold treats lever
 simp only [map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
 simp [diagonal,mul_ite]; simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum]; congr 1; rw [coin,paid,earning_comm]; -- inspect

def readOn (v:γ) : poly Λ→ₐ[ℂ] ℂ:= MvPolynomial.aeval (fun i=> (↑(Spiral.tone (see i) v):ℂ))
private lemma reconcile (p:poly Λ) (v:γ) : readOn v p=Spindle.text (fun i:L=> Spiral.tone i v) (exchange (lever n) p) := by
 unfold Spindle.text readOn; rw [reads_val]; congr 2; funext i; unfold reads lever; simp_rw [map_sum,Finsupp.linearCombination_single, smul_eq_mul,← Complex.ofReal_mul,← Complex.ofReal_sum]
 -- paid,tone & costate sum (tone_i v)=overlap
 congr 1
 exact (expense (see i) v).symm
private lemma tone_sum {I:Type*}[Fintype I] (t:I→γ)(r:I→ℝ)(p : L) : Spiral.tone p (∑ i,r i • t i)=∑ i,r i*Spiral.tone p (t i):= by
 -- derive via raw curl direct add+smul
 let g : γ →ₗ[ℝ] ℝ:=
   { toFun:= Spiral.tone p, map_add':=fun a b=> by
       unfold Spiral.tone; simp_rw [rawCoil,show collect G (a+b)= collect G a+ collect G b from rfl,crease_add]; rfl
     map_smul':=fun r a=> by
       unfold Spiral.tone; simp_rw [rawCoil,show collect G (r • a)=r • collect G a from rfl]; simp only [crease,Orb.Curl,Pi.smul_apply,← smul_sub,← smul_add]; rfl }
 change g _= _; rw [map_sum]; simp_rw [map_smul]; rfl
private lemma labor (w : Mask (FaceAt n) G) (p : poly Λ) :
    let c (i:L) := w i.1 i.2
    display w (exchange (lever n) p)= readOn (∑ i:L, c i • fold i) p := by
 intro c; unfold display readOn; rw [reads_val]; congr 2; funext i; unfold reads lever
 simp_rw [map_sum,Finsupp.linearCombination_single,smul_eq_mul,tone_sum,← Complex.ofReal_mul,← Complex.ofReal_sum]; congr 1; apply Finset.sum_congr rfl; intro k _; rw [paid_eq,mul_comm]
lemma projectedHeat {p q: poly Λ}(h: ∀ v:γ,readOn v p=readOn v q) (v:γ) : readOn v (milk (rig n) p)=readOn v (milk (rig n) q):= by
 rw [reconcile,reconcile,← loft,← prepared,← prepared, show exchange (lever n) p=exchange (lever n) q from touchable fun w=> by rw [labor, labor, h]]
end YM.FormalOPE.RG10.Spiral
