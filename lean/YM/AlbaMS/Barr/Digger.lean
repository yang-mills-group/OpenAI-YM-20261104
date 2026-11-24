import YM.AlbaMS.Cutis.Hot

/-!
# Graded acyclicity setup

Prove linear derivators on Coil from polynomial certificate. applies also over
Tag ring or mass/smooth dimension. Uses Heg & rank positive. no analytic inverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function LinearMap
open scoped BigOperators Classical
variable {ι R E W : Type*} [CommRing R] {ρ : ι→ Bool} {s:Finset ι}{F G: Coil ρ R}{n m:ℕ}{p q r : Bool}
variable [Algebra ℚ R] (P T:Module.End R (Coil ρ R))
def dig (R:Type*)[CommRing R][Algebra ℚ R](n:ℕ):= algebraMap ℚ R ((n:ℚ)⁻¹)
lemma digN (h:0<n): dig R n*(n:R)=1:=by rw [dig,← map_natCast (algebraMap ℚ R) n, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast h.ne'),map_one]
lemma dug (h:0<n) (F:Coil ρ R): dig R n • ((n:R) • F)=F:= by rw [smul_smul,digN h,one_smul]

/-- generation by variables of individual Coil, in fixed Cap, ℚ algebra rings. -/
lemma evolve (U:Submodule R (Coil ρ R))(hU:1∈U)(ht:∀ i∈s,∀ F ∈ U,varC R ρ i*F∈U)(h:FinRank F)(H:Inside (s:Set ι) F): F∈U:= by
  obtain ⟨n,hn⟩:=h
  suffices ∀ m,∀ (F:Coil ρ R), Inside (s:Set ι) F → Heg m F → F∈ U by rw [← ranks _ _ hn]; exact U.sum_mem fun i _=> this _ _ (rankn.inside F i H) (rankn.heg F i)
  intro m F hv hp; induction m generalizing F with
  | zero=> have he := (hp.cap F 0).eroded; rw [show F=(F []) • (1:Coil ρ R) from he.trans (by rw [← put_smul_left,mul_one])]; exact U.smul_mem _ hU
  | succ m ih=>
    have he:germ s F∈U:= U.sum_mem (fun i hi=>ht _ hi _ (ih _ (hv.dz _) (hp.D_zone _)))
    rw [germ_eq _ _ _ hv hp] at he; exact (dug (m.succ_pos) F) ▸ U.smul_mem _ he

omit [Algebra ℚ R] in
def Exo (p:Bool) (P:Module.End R (Coil ρ R)):Prop:=∀ F G, P (F*G)=P F*G+plane p F*P G
omit [Algebra ℚ R] in
def Polar (p:Bool)(P:Module.End R (Coil ρ R)):Prop:=∀ p',∀ F,Tone p' F→Tone (xor p p') (P F)
omit [Algebra ℚ R] in
lemma Exo.cube (h:Exo p P) : P 1=0:=by have he:= h 1 1; rw [mul_one, mul_one, plane_one,one_mul] at he; simpa using he.symm
omit [Algebra ℚ R] in
lemma Exo.term (h:Exo p P)(r:R): P (put ρ r)=0:=by rw [show put ρ r=r • (1:Coil ρ R) from by rw [← put_smul_left,mul_one], map_smul, h.cube P, smul_zero]
omit [Algebra ℚ R] in
lemma Exo.build (v:ι→Coil ρ R)(h:∀ i∈s,Tone (xor p (ρ i)) (v i)): Exo p (tom s v) := by
  intro F G; simp_rw [tom_apply, Finset.sum_mul, Finset.mul_sum,mulD, mul_add]; rw [Finset.sum_add_distrib]; refine congr_arg₂ _ (Finset.sum_congr rfl fun i _=> by rw [mul_assoc]) (Finset.sum_congr rfl fun i hi=>?_); rw [← mul_assoc, (h i hi).slider, plane_twice, Bool.xor_assoc, Bool.xor_self, Bool.xor_false,mul_assoc]
omit [Algebra ℚ R] in
lemma Polar.build (v:ι→Coil ρ R)(h:∀ i∈s,Tone (xor p (ρ i)) (v i)): Polar p (tom s v):= by
  intro q F he; rw [tom_apply]; refine Tone.sum _ _ fun i hi=>?_ ; have hh:= (h i hi).mul (he.dz i); rw [show xor (xor p (ρ i)) (xor q (ρ i)) = xor p q by cases p<;>cases q<;>cases ρ i<;>rfl] at hh; exact hh
omit [Algebra ℚ R] in
lemma tone_p (h:Polar true P) : P (plane true F) = -plane true (P F):=by rw [peels F]; simp_rw [map_add,(peel_tone (p:=true) (F:=F)).pl,(peel_tone (p:=false) (F:=F)).pl,(h _ _ (peel_tone (p:=true))).pl,(h _ _ (peel_tone (p:=false))).pl]; simp [add_comm]
omit [Algebra ℚ R] in
lemma ordinary (t:Exo true P)(r:Polar true P)(H:Exo true T)(h:Polar true T) : Exo false (P ∘ₗ T + T ∘ₗ P):= by intro F G; simp only [LinearMap.comp_apply,LinearMap.add_apply, (show ∀ x y,P (x*y)=_ from fun x y=> t x y), (show ∀ x y,T (x*y)=_ from fun x y=> H x y),map_add,polar_false (F:=F), tone_p P r, tone_p T h, plane_twice,Bool.xor_self, add_mul,mul_add,neg_mul]; abel
lemma extend (p)(h:Exo p P)(H:Exo p T)(he:∀ i∈s,P (varC R ρ i)=T (varC R ρ i))(hr:FinRank F)(hv:Inside (s:Set _) F): P F=T F:=by
  refine sub_eq_zero.mp (evolve (LinearMap.ker (P-T)) ?_ ?_ hr hv); · change P 1-T 1=0; rw [h.cube P,H.cube T,sub_self]
  intro i hi F hF; change P F-T F=0 at hF; change P _- T _=0; rw [h, H, he i hi,sub_eq_zero.mp hF,sub_self]

-- Euler Q/R, rank projections
structure Rises (P: Module.End R (Coil ρ R)):Prop where
 ranks {F : Coil ρ R}{n:ℕ}: Heg n F→Heg n (P F)
namespace Rises
variable {P}
omit [Algebra ℚ R] in
lemma from_axis (v:ι→Coil ρ R)(h:∀ i∈s,Heg 1 (v i)): Rises (tom s v) :=by
  constructor; intro F n hf; cases n with| zero=> rw [(hf.cap _ _).eroded]; simp [tom_apply,Heg.zero]
                                          | succ n=> rw [tom_apply]; rw [Nat.add_comm]; exact Heg.sum _ _ fun i hi=> (h i hi).mul (hf.D_zone i)
omit [Algebra ℚ R] in
lemma ker (h:Rises P)(hf:Cap F n): Cap (P F) n:=by rw [← Coil.ranks _ _ hf,map_sum]; exact Cap.sum _ _ fun i hi=> ((h.ranks (rankn.heg F i)).cap _ _).up (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
omit [Algebra ℚ R] in
lemma leads (h:Rises P)(hv:FinRank F): FinRank (P F):=⟨_,h.ker hv.choose_spec⟩
omit [Algebra ℚ R] in
lemma takeout (h:Rises P)(hv:FinRank F)(hq:P F=0): P (rankn n F)=0:=by
  obtain ⟨N,H⟩:=hv
  by_cases ha:n≤N
  · rw [← Coil.ranks _ _ H,map_sum] at hq; have ht:P (rankn n F)=rankn n (∑ i∈ Finset.range (N+1), P (rankn i F)):=by
      rw [map_sum,Finset.sum_eq_single n, (h.ranks (rankn.heg F n)).criterion]; intro i hi hiv; ext l; rw [rankn_read]; split; exact not_not.1 fun hl=> hiv (_root_.Eq.trans (h.ranks (rankn.heg F i) l hl).symm ‹l.length=n›); rfl
      simp [ha]
    rw [ht,hq,map_zero]
  rw [show rankn n F=0 from ?_,map_zero]; ext l; rw [rankn_read]; split; exact not_not.1 (fun hv=> ha (‹l.length=n› ▸ H l hv)); rfl
end Rises
end YM.MSBar.Bric.Coil
