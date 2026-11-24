import YM.FormalBulk08.Cork.Fine

/-! Reexpress under g = g' H(g'), rescaled coordinates with REAL links
kept. Input and output are *both* in Pap. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wine
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {V I : Type}
abbrev Pence := PowerSeries ℝ
variable (H U : Pence)

def worm (V : Type) : Pence→+*Pap V := PowerSeries.map MvPolynomial.C
lemma worm_roam (z: V→ Pap I) (q : Pence) : roam ℝ z (worm V q) = worm I q := by
   unfold roam worm; rw [change_after]; rw [←pure_map,show (insertAt ℝ z).comp MvPolynomial.C = C.comp MvPolynomial.C from RingHom.ext fun a=>by simp]

def glass (V : Type): Pap V:= worm V H*X
lemma grass : coeff 0 (glass H V)=0:= by rw [glass,coeff_zero_eq_constantCoeff_apply,map_mul];simp
def carver (U : Pence) (V:Type) : V→Pap V:= fun v=>worm V U * C (MvPolynomial.X v)
def canter (V : Type) : Pap V→+*Pap V := (roam ℝ (carver U V)).comp ((substAlgHom (R:=Glyphs ℝ V) (tribe (grass H (V:=V)))).toRingHom)
lemma canter_eq (p:Pap V) : canter H U V p = roam ℝ (carver U V) (p.subst (glass H V)) := by rw [canter,RingHom.comp_apply]; apply congr_arg; change substAlgHom (R:=Glyphs ℝ V) _ p=_; rw [coe_substAlgHom]
lemma steam {p q : Pap V} {n : ℕ} (h: Through n p q) : Through n (canter H U V p) (canter H U V q) := by rw [canter_eq,canter_eq]; exact Through.change_congr (insertAt ℝ (carver U V)) (h.compose (Through.exact_eq (glass H V) n) (grass H))
lemma canter_C {q:TypeR V} : canter H U V (C q)= insertAt ℝ (fun v:V=> worm V U*C (MvPolynomial.X v)) q := by
   rw [canter_eq,subst_C]; exact change_C (insertAt ℝ (carver U V)) q
lemma canter_X : canter H U V X= glass H V:= by
   rw [canter_eq,subst_X (tribe (grass H)),glass,map_mul,worm_roam,roam,change_X]

variable [Fintype V]
lemma loaf (r : ℕ)(T:Tile V r) : canter H U V (C (facade r T))= (worm V U)^r * C (facade r T) := by
   rw [canter_C]; simp_rw [facade_eq,map_sum,Finset.mul_sum];refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [cards,map_mul, map_prod,insert_C,insert_X,Finset.prod_mul_distrib]; simp; ring
lemma tremble (r n:ℕ)(q: TypeR V)(hp:q.IsHomogeneous r) : canter H U V (C q * X^n)= worm V (H^n*U^r)* C q * X^n := by
   have he := loaf H U r (marble r q); rw [marble_grade, MvPolynomial.homogeneousComponent_eq_self hp] at he
   rw [map_mul,map_pow, canter_X, he,glass,map_mul,map_pow,map_pow,mul_pow]; ring

omit [Fintype V] in
lemma snow (F : V→Pap I) (c: ℝ): roam ℝ F (C (MvPolynomial.C c))=C (MvPolynomial.C c) := by simp [roam]

lemma clearing (hu : H*U=1) (q:Pap V)(hp : ∀ i,(coeff i q).IsHomogeneous (i+1)) : canter H U V q= worm V U * q:= by
   ext1 n; rw [(steam H U (dict q n)).apex,((Through.exact_eq (worm V U) n).mul (dict q n)).apex]; simp_rw [map_sum, Finset.mul_sum,map_sum]; refine Finset.sum_congr rfl fun i _=> ?_; apply congr_arg (coeff n); rw [tremble H U (i+1) i _ (hp i),pow_succ,←mul_assoc,←mul_pow,hu,one_pow,one_mul,mul_assoc]
omit [Fintype V] in
lemma calming (hu : H*U=1) (F : V→Pap I) [Fintype I] (hp : ∀ v k,(coeff k (F v)).IsHomogeneous (k+1)) (q:Pap V) : canter H U I (roam ℝ F q)=roam ℝ F (canter H U V q) := by
   have hd (p:TypeR V) : canter H U I (roam ℝ F (C p))=roam ℝ F (canter H U V (C p)) := by
      induction p using MvPolynomial.induction_on with
      | C a => rw [snow,canter_C,canter_C,insert_C,insert_C];exact (snow F a).symm
      | add a b ha hb=> simp_rw [map_add,ha,hb]
      | mul_X p i hh=>
         have hx: canter H U I (roam ℝ F (C (MvPolynomial.X i)))=roam ℝ F (canter H U V (C (MvPolynomial.X i))) := by
           rw [show roam ℝ F (C (MvPolynomial.X i))=F i from (by simp [roam]), canter_C, insert_X,map_mul,worm_roam, clearing H U hu _ (hp i)]; simp [roam]
         simp_rw [map_mul,hh,hx]
   have hg : roam ℝ F (X: Pap V)= X:=by simp [roam]
   have hh : roam ℝ F (canter H U V X)=canter H U I X:= by rw [canter_X,canter_X,glass,map_mul,hg,worm_roam];rfl
   have hz (n): Through n (roam ℝ F q) (roam ℝ F (∑ i∈Finset.range (n+1), C (coeff i q)*X^i)):= Through.change_congr _ (dict q n)
   have hj (n): Through n (roam ℝ F (canter H U V q)) (roam ℝ F (canter H U V (∑ i∈Finset.range (n+1), C (coeff i q)*X^i))) := Through.change_congr _ (steam H U (dict q n))
   ext1 n;rw [(steam H U (hz n)).apex,(hj n).apex]; simp_rw [map_sum,map_mul,map_pow,hg,hd,hh]
end YM.FormalBulk08.Wine
