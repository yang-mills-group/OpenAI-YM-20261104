import YM.Integration.WilsonSeparatedPrefixCanonicalPostAdd
import YM.Integration.WilsonSeparatedPrefixCanonicalFares
import YM.Integration.WilsonSeparatedPrefixCanonicalSoft
import YM.Integration.WilsonSeparatedPrefixCanonicalForced

/-! A complete finite original reporter can put each of its nonempty marked hard profiles
and every one of its mixed entries on the very same zero-ride board. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalZeroPost
open Finset Function MeasureTheory Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal
open MergeProof MergeProof.Accent Extra.Histories Lodestar
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {o:V → Site n}
omit [Fintype V] in
private theorem family {I:Type} [DecidableEq I] {J:Census V} {t:ℝ}
    (s:Finset I) {h:I → Support n → Config G n → Poly J} {k:I → Box n → Config G n → Poly J}
    {H:Support n → Config G n → Poly J} {K:Box n → Config G n → Poly J}
    (parts:∀v∈s,Carton o (h v) (k v) t) (base:Carton o H K t) :
    Carton o (fun Z U=>(∑v∈s,h v Z U)+H Z U) (fun b U=>(∑v∈s,k v b U)+K b U) t := by
  induction s using Finset.induction_on with
  | empty=>simpa only [sum_empty,zero_add] using base
  | @insert v s hv ih=>
    have next:=WilsonSeparatedPrefixCanonicalPostAdd.cartons (parts v (mem_insert_self ..))
      (ih (fun i hi=>parts i (mem_insert_of_mem hi)))
    simpa only [sum_insert hv,add_assoc] using next

variable (P:Rep G n) (w:V → ℝ) (pos:∀v,0<w v) {e:ℝ} {a b:ℝ}
  (M:V → Support n → Config G n → Poly (Marks V)) (h:V → Box n → Config G n → ℂ)
  {H:Support n → Config G n → Poly (Marks V)} {K:Box n → Config G n → Poly (Marks V)}
  {m k:V → ℝ}
local notation "w₂" => (fun v:V=>w v^2)
local notation "S" => (Marks V)
local notation "T" => (Marks (V×Bool))
local notation "named" => (fun (v:V) b U=>Poly.send ((S).fire v) (h v b U))
local notation "upper" => (fun Z U=>(∑v,duplicate V (M v Z U))+duplicate V (H Z U))
local notation "lower" => (fun (z:ℂ) b U=>(∑v,z • duplicate V (named v b U))+duplicate V (K b U))

include pos in
theorem original (cart:Carton o H K P.p.threshold)
    (healthy:∀v Z,Burns o Z (M v Z) P.p.threshold)
    (flag:∀v b,Flow o b (fun U=>named v b U) P.p.threshold)
    (soft:Towed w₂ id H P.p.B e a) (hard:Towed w₂ Prod.fst K P.p.B e b)
    (locals:∀v,Towed w₂ id (M v) P.p.B e (m v))
    (keys:∀v,Towed w₂ Prod.fst (named v) P.p.B e (k v))
    (z:ℂ) (regularFare:(∑v,m v)+a≤1) (hardFare:(∑v,‖z‖*k v)+b≤1):
    Served P (fun (_:V×Bool) _=>0) (fun (_:V×Bool) _ _=>0)
      (restore P (fun (_:V×Bool) _=>0) (fun (_:V×Bool) _ _=>0) upper (lower z))
      (o ∘ Prod.fst) (w ∘ Prod.fst) e 1 := by
  have one(v:V):Carton (o ∘ Prod.fst) (fun Z=>duplicate V ∘ M v Z)
      (fun b=>duplicate V ∘ named v b) P.p.threshold := by
    refine ⟨fun Z=>burns_duplicate (healthy v Z),fun b=>⟨flow_duplicate (flag v b),fun U=>large_duplicate ?_⟩⟩
    rw [Poly.part_send,if_neg (Ne.symm (Census.fire_hot _ v))]
  have scaled(v:V):Carton (o ∘ Prod.fst) (fun Z=>duplicate V ∘ M v Z)
      (fun b U=>z • duplicate V (named v b U)) P.p.threshold :=
    ⟨(one v).exp,(WilsonSeparatedPrefixCanonicalCarton.rescale (one v) z).flag⟩
  have wp(i:V×Bool):0<(w ∘ Prod.fst) i:=pos _
  refine ⟨_,_,family univ (fun i _=>scaled i) (WilsonSeparatedPrefixCanonicalPostAdd.twin cart),?_,?_,rfl⟩
  · exact (WilsonSeparatedPrefixCanonicalFares.add_family univ (fun v _=>towed_duplicate w (locals v))
      (towed_duplicate w soft)).shrink le_rfl regularFare wp
  · exact (WilsonSeparatedPrefixCanonicalFares.add_family univ
      (fun v _=>WilsonSeparatedPrefixCanonicalFares.scale (towed_duplicate w (keys v)) z)
      (towed_duplicate w hard)).shrink le_rfl hardFare wp

end YM.Integration.WilsonSeparatedPrefixCanonicalZeroPost
end
