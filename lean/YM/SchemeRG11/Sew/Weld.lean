import YM.SchemeRG11.Sew.Samples
/-! Subalgebra price principle for closed Wick insertions.
 Peers contracted at most once per leg. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Sew
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt
open scoped Classical
variable {I J K U:Type*} [DecidableEq I] (D:Dose U ℝ)
lemma fondle (p q:Paper U ℝ)(a:Stem U ℝ):D.avg ((D.neg.heat (leaf a*p))*q) = D.avg (D.neg.heat p * vent (D.windfall a) q) := by
 rw [D.zeph_neg,sub_mul,map_sub,mul_assoc,D.release_leaf,vent_l,map_add,mul_comm (vent _ (D.neg.heat _))]; abel -- order
abbrev array(J U:Type*):=J→ Paper U ℝ
def screen (s:Finset I)(L:I→ J→ K→ Stem U ℝ)(p:I→Paper K ℝ):array J U:=fun x=>∏ i∈s,D.neg.heat (vary (L i x) (p i))
def Strain(D:Dose U ℝ)(M:J→ Stem U ℝ)(F:array J U):array J U:=fun x=>vent (D.windfall (M x)) (F x)
def flood(D:Dose U ℝ)(Z:List (J→ Stem U ℝ))(F:array J U):array J U:= match Z with
| []=> F
| a::Z=>flood D Z (Strain D a F)
abbrev Gate(S:Subalgebra ℝ (J→ℝ))(Z:Set (J→ Stem U ℝ))(F:array J U):Prop:=∀ L:List (J→ Stem U ℝ),(∀i∈L,i∈Z) → (fun x=> MvPolynomial.aeval (R:=ℝ) (fun _:U=>(0:ℝ)) (Sew.flood D L F x))∈ S
namespace Gate
variable {S:Subalgebra ℝ (J→ℝ)}{Z:Set (J→Stem U ℝ)}{A B: array J U}
omit [DecidableEq I] in -- check unused I
lemma rose {F: J→Stem U ℝ}(h:Gate D S Z A)(p:F∈Z): Gate D S Z (Strain D F A):= fun t ht=>h (F::t) fun i w=> (by
   rcases List.mem_cons.mp w with e|e; · rw [e]; exact p
   exact ht i e) -- indent
lemma swell(Z:Set (J→Stem U ℝ)): Gate D S Z 0:=by
 intro i h; have he(L:List (J→ Stem U ℝ)): Sew.flood D L 0=0:=by induction L with
   | nil=>rfl
   | cons z t ih=>rw [Sew.flood, show Strain D z 0=0 from funext (fun _=>map_zero _),ih]
 change _∈S; convert S.zero_mem using 1; funext x; rw [show Sew.flood D i _=0 from he i]; exact map_zero _
lemma billS{f:J→ℝ}(p:f∈S) :Gate D S Z (fun x=>C (f x)):=by
 intro i h; cases i with
 | nil=> simpa only [Sew.flood,aeval_C,Algebra.algebraMap_self_apply] using p -- direction?
 | cons a i=>
    rw [show Sew.flood D (a::i) (fun x=>C (f x)) = Sew.flood D i 0 from by rw [Sew.flood, show Strain D a (fun x=>C (f x))=0 from funext fun _=>vent_C ..]]; apply swell _ Z i fun j w=> h j (by simp [w])
lemma accrue(t:List (J→Stem U ℝ))(A B:array J U):Sew.flood D t (A+B)=Sew.flood D t A+ Sew.flood D t B:=by induction t generalizing A B with
    | nil=>rfl
    | cons i t ih=> rw [Sew.flood,show Strain D i (A+B)=Strain D i A+Strain D i B from funext fun r=> map_add ..,ih];rfl

lemma addS(h:Gate D S Z A)(e:Gate D S Z B):Gate D S Z (A+B):=by
 intro t ht; apply Eq.mp _ (S.add_mem (h t ht) (e t ht)); congr 1; funext x
 rw [accrue]; exact (map_add ..).symm
lemma scales {f:J→ℝ}(h:f∈S)(p:Gate D S Z A):Gate D S Z (fun x=> f x • A x):=by
 intro t ht; have he (t:List (J→ Stem U ℝ))(A:array J U): Sew.flood D t (fun x=> f x • A x)=fun x=> f x • Sew.flood D t A x:=by induction t generalizing A with
    | nil=>rfl
    | cons a t ih=> rw [Sew.flood, show Strain D a (fun x=>f x • A x)=_ from (show _=(fun x=>f x • Strain D a A x) from funext fun x=> (vent _).map_smul _ _),ih];rfl
 simp only [he,map_smul]; exact S.mul_mem h (p t ht)
lemma trunks {F:J→Stem U ℝ}(p:Gate D S Z A)(h:∀ W∈Z,(fun x=> D.bed (F x) (W x))∈ S) : Gate D S Z (fun x=>leaf (F x)* A x):=by
 intro t ht; induction t generalizing A with
 | nil=> simp only [Sew.flood,map_mul,Haze.realTaste]; have he(x:J): sense (fun _:U=>(0:ℝ)) (F x)=0:=by simp [sense,Finsupp.linearCombination_apply,Finsupp.sum];
         simp only [he,zero_mul]; exact S.zero_mem
 | cons a t ih=>
   have hw:a∈Z:=ht _ (by simp); have hs:=h a hw; have hu (i:J→ Stem U ℝ)(hy:i∈t):i∈Z:= ht _ (by simp [hy]);
   -- distribute strain; IH only length t, addS can't use on full product + right, use point-linear
   let c(x):=D.bed (F x) (a x)
   have H:Strain D a (fun x=>leaf (F x)* A x)= (fun x=> leaf (F x)*Strain D a A x) + fun x=>c x • A x:=by
      funext x; unfold Strain; rw [Pi.add_apply,vent_l,taste,mul_comm (A x) ]; unfold c; rw [C_mul',D.bed_comm (F x) (a x)]; rfl -- repair
   simp only [Sew.flood,H, accrue, Pi.add_apply,map_add]; exact S.add_mem (ih (rose D p hw) hu) (Gate.scales D hs p t hu)
end Gate
end YM.SchemeRG11.Sew
