import YM.RG02.Wick.Pairs

/-! Retain a line choice as a second set of marks. The projection forgetting
this information is multiplicative only on the appropriate subalgebra
(disjoint full pairings). This proves the exact assembly law at each fixed
pairing, not just factorization statements about already-summed statistics. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Wick
open Filter Marker Multi Finset Extra.Trajectories Marks Remove Next.Rank Next.Rank.Normal
open scoped BigOperators Classical
variable {A V : Type} [DecidableEq A] [Fintype A] [DecidableEq V] {R : Census V}

def arms (o : A → V)(v : Finset V) := Finset.univ.filter fun a : A => o a∈v
omit [DecidableEq A] in
@[simp] lemma arm_of {o : A → V}{a v} : a∈arms o v ↔ o a∈v := by simp [arms]

def Paired (o : A → V)(t : (together R (Lines A)).Mode) := CompleteOn (arms o (Pair.fst t).val) (Pair.snd t)
instance (o : A → V)(t : (together R (Lines A)).Mode) : Decidable (Paired o t) := by unfold Paired; infer_instance

lemma paired_join {o : A → V}{s t r : (together R (Lines A)).Mode}
    (hs : Paired o s)(ht : Paired o t)(hr : Poly.merges s t r) : Paired o r := by
  nth_rw 1 [← Pair.mk_read s, ← Pair.mk_read t, ← Pair.mk_read r] at hr
  obtain ⟨ha,hp⟩ := (Pair.merges ..).mp hr
  constructor
  · rw [← (merge_union hp).2, hs.1,ht.1, ← ha.2]; ext; simp
  intro i hi; have he := mem_union.mp (hp.2.symm ▸ hi); exact he.elim (hs.2 i) (ht.2 i)

lemma paired_coexist {o : A→V}{s t : (together R (Lines A)).Mode}
    (hs : Paired o s)(ht : Paired o t){r : R.Mode}
    (hr : Poly.merges (Pair.fst s) (Pair.fst t) r) : ∃ w, Poly.merges s t w := by
   have hg : Poly.merges (Multi.unionOf (Pair.snd s)) (Multi.unionOf (Pair.snd t)) (given (arms o r.val)) := by
     constructor
     · rw [hs.1,ht.1]
       exact Finset.disjoint_left.mpr fun _ h hx => Finset.disjoint_left.mp hr.1 (arm_of.mp h) (arm_of.mp hx)
     rw [hs.1,ht.1]; dsimp only [given]; rw [← hr.2]; ext; simp
   obtain ⟨w,hw⟩ := merge_union_inv hg
   exact ⟨Pair.mk r w,by simpa only [Pair.mk_read] using (Pair.merges _ _ _ _ _ _).mpr ⟨hr,hw⟩⟩

def Retains (o : A → V)(x : Poly (together R (Lines A))) := ∀ t, ¬ Paired o t → x.part t=0

lemma paired_quiet (o : A → V) : Paired o (together R (Lines A)).quiet := by
  unfold Paired
  rw [Pair.fst_quiet,Pair.snd_quiet]; unfold CompleteOn Lines
  simp [arms,Census.quiet,Multi.unionOf]

lemma paired_zeroth (o : A → V)(p : (Lines A).Mode) : Paired o (Pair.mk R.quiet p) → p=(Lines A).quiet := by
  intro h; unfold Paired at h; rw [Pair.fst_mk,Pair.snd_mk] at h
  have hg : Multi.unionOf p=(full A).quiet := Subtype.ext (h.1.trans (by ext; simp [Census.quiet]))
  have hv : p∈shards _ (full A).quiet := (chooses ..).mpr hg
  rw [shards_quiet] at hv
  exact Finset.mem_singleton.mp hv

/-- Projection on moments that retain lines (not a universal map!). -/
def unframe (R : Census V) {I : Type}[DecidableEq I](Q : Census I) : Poly (together R Q) →ₗ[ℂ] Poly R where
  toFun x := Poly.inject fun s => ∑ p : Q.Mode, x.part (Pair.mk s p)
  map_add' x y := Poly.ext fun s => by
    rw [Poly.part_plus]
    change (∑ p : Q.Mode, (x+y).part (Pair.mk s p)) = (∑ p : Q.Mode, x.part (Pair.mk s p)) + ∑ p : Q.Mode, y.part (Pair.mk s p)
    simp_rw [Poly.part_plus]; exact sum_add_distrib
  map_smul' r x := by
    ext s
    rw [RingHom.id_apply, Poly.part_smul]
    change (∑ p : Q.Mode, (r • x).part (Pair.mk s p)) = r * ∑ p : Q.Mode, x.part (Pair.mk s p)
    simp_rw [Poly.part_smul, mul_sum]


def compress (R : Census V)(A : Type)[DecidableEq A][Fintype A] := unframe R (Lines A)

lemma unframe_part {I : Type}[DecidableEq I](Q : Census I)(x : Poly (together R Q))(s : R.Mode) :
    (unframe R Q x).part s=∑ p : Q.Mode,x.part (Pair.mk s p) := rfl
lemma compress_part (x : Poly (together R (Lines A)))(s : R.Mode) :
    (compress R A x).part s=∑ p : (Lines A).Mode,x.part (Pair.mk s p) := unframe_part _ _ _

lemma compress_send (t : (together R (Lines A)).Mode) (c : ℂ) :
    compress R A (Poly.send t c)=Poly.send (Pair.fst t) c := by
  ext s
  nth_rw 1 [← Pair.mk_read t]
  rw [compress_part,Poly.part_send]; simp_rw [Poly.part_send, Pair.mk_inj]
  by_cases h : s=Pair.fst t <;> simp [h]

namespace Retains
variable {o : A → V}{x y : Poly (together R (Lines A))}
lemma zero (o : A → V) : Retains (R:=R) o 0 := fun _ _ => rfl
lemma one (o : A → V) : Retains (R:=R) o 1 := by
  intro s hn
  rw [Poly.one_part,if_neg (fun (h : s=(together R (Lines A)).quiet)=> hn (h.symm ▸ paired_quiet o))]
lemma mul (h : Retains o x)(g : Retains o y) : Retains o (x*y) := by
  intro s hs; rw [Poly.part_mul]; apply sum_eq_zero
  intro r _; apply sum_eq_zero; intro t _; split
  next hv =>
    by_cases h' : Paired o r
    · rw [g t (fun hh => hs (paired_join h' hh hv)),mul_zero]
    rw [h r h',zero_mul]
  rfl
lemma add (h : Retains o x)(g : Retains o y) : Retains o (x+y) := fun t ht => by rw [Poly.part_plus,h _ ht,g _ ht,add_zero]
lemma sub (h : Retains o x)(g : Retains o y) : Retains o (x-y) := fun t ht => by rw [Extra.Trajectories.part_sub,h _ ht,g _ ht,sub_zero]
lemma smul (h : Retains o x)(c : ℂ) : Retains o (c • x) := fun t ht => by rw [Poly.part_smul,h _ ht,mul_zero]
lemma fin_sum {I : Type*} (s : Finset I)(f : I → Poly (together R (Lines A)))(h : ∀ i∈s,Retains o (f i)) : Retains o (∑ i∈s,f i) := by
  intro t ht; rw [Poly.part_sum]; exact sum_eq_zero fun i hi => h i hi t ht
lemma pow (h : Retains o x)(i : ℕ) : Retains o (x^i) := by induction i with
  | zero => rw [pow_zero]; exact one o
  | succ i ih => rw [pow_succ]; exact ih.mul h

lemma compress_one : compress R A 1=1 := compress_send (together R (Lines A)).quiet 1

lemma multiply (h : Retains o x)(g : Retains o y) : compress R A (x*y) = compress R A x*compress R A y := by
   let C := compress R A
   have he (s t : (together R (Lines A)).Mode) :
       C (Poly.send s (x.part s) * Poly.send t (y.part t)) =
         C (Poly.send s (x.part s)) * C (Poly.send t (y.part t)) := by
     unfold C
     by_cases hp : Paired o s; swap; · simp [h s hp]
     by_cases ht : Paired o t; swap; · simp [g t ht]
     rw [compress_send,compress_send]
     by_cases hx : ∃ w, Poly.merges s t w
     · obtain ⟨w,hw⟩ := hx
       have hh : Poly.merges (Pair.fst s) (Pair.fst t) (Pair.fst w) := by
         nth_rw 1 [← Pair.mk_read s, ← Pair.mk_read t, ← Pair.mk_read w] at hw
         exact ((Pair.merges ..).mp hw).1
       rw [send_prod hw,compress_send,send_prod hh]
     rw [send_noProd hx, map_zero, send_noProd (fun HH => hx (HH.elim fun _ hr => paired_coexist hp ht hr))]
   change C _=C _*C _
   rw [← Poly.studs x,← Poly.studs y]
   simp_rw [sum_mul,mul_sum,map_sum,he,sum_mul,mul_sum]

lemma powers (h : Retains o x)(k : ℕ) : compress R A (x^k)=(compress R A x)^k := by
  induction k with
  | zero => rw [pow_zero,pow_zero,compress_one]
  | succ k ih => rw [pow_succ, pow_succ,multiply (h.pow k) h,ih]
lemma quiet (h : Retains o x) : (compress R A x).part R.quiet=x.part (together R (Lines A)).quiet := by
  rw [compress_part,sum_eq_single (Lines A).quiet, Pair.quiet]
  · exact fun i _ hi => h _ (hi ∘ paired_zeroth o i)
  simp
variable [Fintype V]
lemma preserves (h : Retains o x)(hx : x.part (together R (Lines A)).quiet=0) :
    compress R A (Poly.pass x)=Poly.pass (compress R A x) := by
   rw [pass_extended (compress R A x) (h.quiet.trans hx) (N:=Fintype.card (V ⊕ Multi.Hot (full A))) (by simp),Poly.pass,map_sum]; simp_rw [map_smul,h.powers]
lemma exponent (h : Retains o x) : Retains o (Poly.pass x) := Retains.fin_sum _ _ fun k _ => (h.pow k).smul _
lemma logged (h : Retains o x)(hx : x.part (together R (Lines A)).quiet=1) : Retains o (connected x) := by
  rw [connected_eq_logTable hx]
  exact Retains.fin_sum _ _ fun i _ => (((h.sub (one o)).pow (i+1)).smul _)
lemma relates (h : Retains o x)(hx : x.part (together R (Lines A)).quiet=1) :
    compress R A (connected x)=connected (compress R A x) := by
  have hh := h.logged hx; have hz := connected_quiet hx
  apply Extra.Trajectories.pass_inj (hh.quiet.trans hz) (connected_quiet (h.quiet.trans hx))
  rw [← hh.preserves hz, pass_connected hx, pass_connected (h.quiet.trans hx)]
end Retains
end YM.RG02.Wick
