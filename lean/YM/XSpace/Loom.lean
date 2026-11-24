import YM.XSpace.Bilocal
/-! # Slot gathering in arbitrary separated tests -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G : Gauge}

def Kept (S:Finset E4)(p: Web G): Prop:= ∀ k∈p.vars, k.1∈S
namespace Kept
variable {p q:Web G} {S:Finset E4}
lemma mono (h:Kept S p){T:Finset E4}(ht:S ⊆ T): Kept T p:= fun i hi=> ht (h i hi)
lemma zero' (S:Finset E4) : Kept S (0:Web G):=fun k h=> False.elim (by simp at h)
lemma one (S:Finset E4) : Kept S (1:Web G):=fun k h=> False.elim (by simp at h)
lemma add (h:Kept S p)(hs:Kept S q): Kept S (p+q):= fun i hi=>((Finset.mem_union.mp (vars_add_subset p q hi))).elim (h i) (hs i)
lemma mul (h:Kept S p)(hs:Kept S q): Kept S (p*q):= fun i hi=>((Finset.mem_union.mp (vars_mul p q hi))).elim (h i) (hs i)
lemma scale (h:Kept S p)(t:ℂ): Kept S (t • p):= by rw [← C_mul']; exact Kept.mul (fun i hi=> by simp at hi) h
lemma sub (h:Kept S p)(hs:Kept S q): Kept S (p-q):= by rw [sub_eq_add_neg, ← neg_one_smul ℂ q]; exact h.add (hs.scale _)
lemma posted {x:E4} (hv:x∈S)(p:WickPol G): Kept S (post x p):= by
  intro k h; obtain ⟨a,hp,ha⟩:= mem_vars_rename _ _ h; exact ha ▸ hv
lemma pair (v w:Flavor 0){x y:E4}(h:x∈S)(he:y∈S): Kept S (signFor x y v w G):= by
  intro i hi; obtain ⟨c,-,hz⟩:=Finset.mem_biUnion.mp (vars_sum_subset _ _ hi)
  exact ((posted h _).mul (posted he _)) i hz
end Kept

inductive Squares (G:Gauge): Finset E4→ Web G→Prop
| one {B}: Squares G B 1
| cons {B q x}(hx:x∉B)(v:Flavor 0): Squares G (insert x B) q→ Squares G B (post x (team G v v)*q)

/-- Null also after further interrogations, can iterate `Bilocal`. -/
def Silent (B:Finset E4)(p:Web G): Prop:= Kept B p ∧ ∀ q,Squares G B q → WW G (q*p)=0


lemma another_square {p: Web G}{B:Finset E4}(h:Silent B p)(v:Flavor 0) {x:E4}(hx:x∉B): Silent (insert x B) (post x (team G v v)*p):= by
  refine ⟨(Kept.posted (Finset.mem_insert_self ..) _).mul (h.1.mono (Finset.subset_insert ..)),fun R hu=>?_⟩
  rw [show R*(post x (team G v v)*p)=post x (team G v v)*R*p by ring]; exact h.2 _ (.cons hx _ hu)

lemma after_pole (c:G.ColorIndex){p:Web G}{B:Finset E4}(h:Silent B p) {x y:E4}(hx:x∉B)(hy:y∉B)(hg:x≠y)(v w: Flavor 0): WW G (signFor x y v w G*p)=0:=by
  let a := (1/2:ℝ) • (x-y); let m:= x-a
  have he : x=m+a:= by unfold m; abel
  have hf : y=m-a:= by unfold m a; module
  have hb : a≠0:= smul_ne_zero (by norm_num) (sub_ne_zero.mpr hg)
  rw [he,hf] -- maybe replaces definitions in hf/h
  apply LocalBill.bilo c B p h.1 (he ▸ hx) (hf ▸ hy) hb
  constructor
  · intro q; rw [← he]; simpa using (h.2 _ (Squares.cons hx q .one))
  · intro q; rw [← hf]; simpa using (h.2 _ (Squares.cons hy q .one))
  intro u q b f ht hv hs; rw [← he, ← hf]; rw [← he] at hv; rw [← hf] at hs
  have h':x ∉ insert f B:= by simp [Ne.symm hv,hx];
  have hw: y ∉ insert x (insert f B):= by simp [Ne.symm hg,Ne.symm hs,hy]
  simpa only [mul_one,mul_assoc] using h.2 _ (Squares.cons (x:=f) ht u (.cons h' q (.cons hw b .one)))

lemma supplements (c:G.ColorIndex){p:Web G}{B:Finset E4}(h:Silent B p) {x y:E4}(hx:x∉B)(hy:y∉B)(hg:x≠y)(v w: Flavor 0): Silent (insert x (insert y B)) (signFor x y v w G*p):=by
  let U:= signFor x y v w G
  refine ⟨(Kept.pair v w (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))).mul (h.1.mono fun z hz=> Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)),fun q hv=>?_⟩
  generalize hh : insert x (insert y B)=S at hv
  induction hv generalizing p B with
  | one => rw [one_mul]; exact after_pole c h hx hy hg v w
  | cons ht u eh ih =>
    rename_i T t z
    rw [← hh] at ht; have hz : z≠x ∧ z≠y ∧ z∉ B:= by simpa only [Finset.mem_insert, not_or] using ht
    rw [show post z (team G u u)*t*(U*p)=t*(U*(post z (team G u u)*p)) by ring]; exact ih (another_square h u hz.2.2) (by simp [hx,Ne.symm hz.1]) (by simp [hy,Ne.symm hz.2.1]) (by rw [← hh,Finset.insert_comm z x,Finset.insert_comm z y])

/-- Closed probes, forbid collisions charged before multiplying. -/
inductive Thread (G:Gauge) : Finset E4→Web G→Prop
| one {B}:Thread G B 1
| scale {B p}: Thread G B p→(t:ℂ)→ Thread G B (t • p)
| add {B p q}:Thread G B p→Thread G B q→Thread G B (p+q)
| join {B p x y} (u v:Flavor 0): x≠y→x∉B→y∉B→Thread G (insert x (insert y B)) p→ Thread G B (signFor x y u v G*p)

lemma Thread.subs {p: Web G} {B:Finset E4}(h:Thread G B p) (c:G.ColorIndex): ∀ P, Silent B P→ WW G (p*P)=0:= by
  induction h with
  | one=>exact fun P h=> h.2 1 .one
  | scale h t ih=> exact fun P h'=> by rw [smul_mul_assoc, map_smul, ih P h',smul_zero]
  | add h he ih iq=> exact fun P hp=> by rw [add_mul,map_add,ih P hp,iq P hp,add_zero]
  | join u v he hs hu h ih =>
    intro P hp
    rename_i p x y -- B?
    rw [show signFor x y u v G*p*P=p*(signFor x y u v G*P) by ring]; exact ih _ (supplements c hp hs hu he u v)

lemma Thread.zero {B}:Thread G B (0:Web G):= by simpa using Thread.scale (B:=B) (G:=G) .one 0
lemma Thread.scalar {B}(c:ℂ):Thread G B (C c:Web G):= by simpa only [← C_mul',mul_one] using Thread.scale (B:=B) (G:=G) .one c
lemma Thread.mono {p:Web G}{B B':Finset E4}(h:Thread G B p)(hb:B'⊆ B):Thread G B' p:= by
  induction h generalizing B' with
  | one=>exact .one
  | add h t H Q=> exact (H hb).add (Q hb)
  | scale h t H=> exact (H hb).scale t
  | join u v he hp hw h ih=> exact .join u v he (fun H=> hp (hb H)) (fun H=> hw (hb H)) (ih (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hb))) -- mt hb applies?
end YM.XSpace.Stab
