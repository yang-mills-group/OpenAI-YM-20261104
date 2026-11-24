import YM.Frontier6.Multi.Seams.Bricks

/-!
# Cotton weights

Criterion retaining actual representations and possible competing readings.
Use `Ultrafilter` below fuse: all Centered from Stamped etc meet same branch
at each finite n. Mix with different heights. No bound on order of Pace or sign.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word Fareway
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{I V:Type}{C:Family G}{H:Extraction.Order}{S:Table C.book}(K:Final C H S)
variable (T:Fareway I) (ξ:Ultrafilter (ℕ×ℕ))
variable {P P' : Type}[Fintype P][Fintype P']{f:P→Type}{f':P'→Type}[_i:∀ p,Fintype (f p)][_j:∀ p,Fintype (f' p)]

abbrev BasisRay (S:Table C.book)(I:Type):= I→ E4→ Spelling S
structure Permit (j k:I→ℕ)(X:BasisRay S I) (a:ℝ) :Prop where
   owns : ∃ (P : Type) (_: Fintype P) (f:P→Type)(_ :∀ p,Fintype (f p)) (Y:I→ Plan C P f)(w:I→ℝ),
       (∀ (p:P) (z:f p), T.Costs (fun i=> C.S.gridPoint (j i) ((Y i).point p z)) (-1)) ∧
       T.Costs w a ∧ ∀ᶠ i in T.via,
           ((Y i).SlotsClear (j i)) ∧ 0 ≤ w i ∧ Centered C ξ (k i) (fun n=> (Y i).cost (j i) n.1 n.2) (w i) ∧
           ∀ z, Tale.Congr K ((Y i).syntaxR (j i) z S) (X i z)

-- Convenient predicate for moving clearances. lower cost as ∥gap∥ ≥ exp...
def ReachWide (T:Fareway I)(x y:I→ E4)(c:ℝ):Prop:=∀ d:ℝ,c<d→∀ᶠ i in T.via, Real.exp (T.scale i * (-d))≤ ‖x i - y i‖
def Wide (T:Fareway I)(x:I→V→ E4)(c:ℝ):Prop:= Pairwise fun i j=> ReachWide T (fun z=>x z i) (fun z=>x z j) c

lemma Fareway.Bench.days {S: Schedule}{T:Fareway I}{k:I→ℕ}{a:ℝ}(h:Bench S T k a)(he:S.Gentle)(n:ℕ): Bench S T (fun i=> k i+n) a:=by induction n with
  | zero=> simpa using h
  | succ n ih=> simpa only [← add_assoc] using! ih.succ he

set_option quotPrecheck false
variable {K T ξ}
section
variable [Fintype V][DecidableEq V]
local notation "M"=> Fintype.card V
local notation "E"=> Fintype.equivFin V
lemma aperture (V:Type)[Fintype V][DecidableEq V](S:Schedule) : ∃ d:ℕ, ∀ (b:ℕ) (r: V→ℕ), (∀ i,b+d≤ r i) → ∀ x:V→ E4, ∃ p:E4,∃ v:V→ Cover,∀ i:V, atStop S b (v i) (3*S.a (r i)) (x i+p):=by
    obtain ⟨d,hd⟩:= Platform.fit_chart S (Fintype.card V)
    refine ⟨d,fun b r hr x=>?_⟩; let E':= Fintype.equivFin V; obtain ⟨p,v,hv⟩:= hd b (points (x ∘ E'.symm)); refine ⟨p,v ∘ E',fun i a=>?_⟩
    obtain ⟨i,rfl⟩:= E'.symm.surjective i; simp only [comp_apply,Equiv.apply_symm_apply]; exact (hv i a).trans_le (sub_le_sub_left (mul_le_mul_of_nonneg_left (S.strictAnti.antitone (hr _)) (by norm_num)) _)
lemma Wide.margin {S:Schedule}{T:Fareway I}{k:I→ℕ}{a b:ℝ}{z:I→V→ E4}(hw:Wide T z a)(hk:Bench S T k b)(hb:a<b):∀ᶠ i in T.via, Pairwise fun j l=>4*S.a (k i)< ‖z i j-z i l‖:=by
    obtain ⟨c,hc,hc'⟩:= exists_between hb
    have hY:= ((T.minted_c 4 (by norm_num)).mul hk.spacing).cheaper (T.minted (-c)) (by linarith : 0+-b < -c)
    filter_upwards [hY,eventually_all.mpr fun j:V=> eventually_all.mpr (fun k:V=> eventually_all.mpr fun h:j≠k=> hw h c hc)] with i hi he j k h using hi.trans_le (he j k h)

variable {N:V→Type}{W: (i:V)→N i→Type}[_h:∀ i,Fintype (N i)][_hc:∀ i p,Fintype (W i p)]
variable (Y:∀ i:V,I→Plan C (N i) (W i))(u:I→ V→ E4)(r:V→I→ℕ)
variable {j k:I→ℕ}{a b:ℝ}{y:V→ℝ}
lemma Wide.land {T:Fareway I} (h:Wide T u a) (he:a<1) (hp:∀ i p s,T.Costs (fun z=> C.S.gridPoint (j z) ((Y i z).point p s)) (-1)) (hz:∀ᶠ n in T.via,∀ x:V,(Y x n).SlotsClear (j n)) :
    ∀ᶠ n in T.via, ∀ x:∀ i,N i, Injective (Plan.landing (fun i=> Y i n) (j n) (u n) x):=by
    obtain ⟨l,hl,hl'⟩:= exists_between he; let z(n):= Real.exp (T.scale n*(-l)); let q(n):= z n/4
    have hT:= T.minted (-l)|>.div (T.minted_c 4 (by norm_num))
    filter_upwards [eventually_all.mpr fun i:V=>eventually_all.mpr fun p:N i=>eventually_all.mpr fun s=> (hp i p s).from_allowance hT (by linarith),hz,eventually_all.mpr fun i:V=>eventually_all.mpr fun j:V=>eventually_all.mpr fun he:i≠j=> h he l hl] with n ho hy hx x
    rintro ⟨i,s⟩ ⟨l,t⟩ h; by_cases hi:i=l
    · subst l; refine congr_arg (Sigma.mk i) ((hy i _ timeAxis) ?_); exact congr_arg (fun p:E4=>p timeAxis) (add_right_cancel h)
    have hz:= hx i l hi; have hL:u n i-u n l= C.S.gridPoint (j n) ((Y l n).point _ t)- C.S.gridPoint (j n) ((Y i n).point _ s):=by
       change C.S.gridPoint _ _ +u n i=C.S.gridPoint _ _ +u n l at h; rw [sub_eq_sub_iff_add_eq_add]; rw [add_comm]; exact h
    rw [hL] at hz
    have ht := norm_sub_le (C.S.gridPoint (j n) ((Y l n).point _ t)) (C.S.gridPoint (j n) ((Y i n).point _ s))
    have he:= (add_le_add (ho l (x l) t) (ho i (x i) s)); have hv:z n≤ q n+q n:= hz.trans (ht.trans he)
    exfalso; unfold q at hv; linarith only [hv, (Real.exp_pos _ : 0< z n)]

lemma budget_product {K:Final C H S}{T:Fareway I}{ξ:Ultrafilter (ℕ×ℕ)} (hξ:ξ.toFilter ≤ H.fuse)(X:V→ BasisRay S I)(c:V→ℝ)(hP:∀ v:V,Permit K T ξ j (r v) (X v) (c v))
    (hb:Bench C.S T k b)(hy:∀ i:V,Bench C.S T (r i) (y i))(hm:∀ i,b < y i)
    (ha:a < b)(he:a < 1)(hw:Wide T u a) (s:I→StateIndex K)(hs:Org.Grill C H) :
     T.Costs (fun i=> poll S (state K (s i)) (∏ v:V,X v i (u i v))) (∑ v:V,c v):=by
    choose N F W hW A Z H U hf using fun v=>(hP v).owns; let _:= F; let _:= hW
    have hM : T.Costs (fun i=> ∏ v:V,Z v i) (∑ v:V,c v):=by
       suffices ∀ S:Finset V,T.Costs (fun i=>∏ v∈S,Z v i) (∑ v∈S,c v) by exact this _
       intro S; induction S using Finset.induction_on with
       | empty=> simp only [Finset.prod_empty, Finset.sum_empty]; exact Costs.const _
       | @insert v S hx ih=> simp_rw [Finset.sum_insert hx, Finset.prod_insert hx]; exact (U v).mul ih
    obtain ⟨d,hd⟩:= aperture V C.S
    apply Costs.allows_norm hM
    have hD:= hw.land A u he H ((eventually_all.mpr hf).mono fun i he v=>(he v).1)
    filter_upwards [ hD, hw.margin hb ha,eventually_all.mpr (fun i:V=> ((hb.days C.path.levels.fits.mesh d).later (hy i) (hm i))), eventually_all.mpr hf] with i hl hx he h;
    let Y:=fun v:V=> A v i; let G:=fun v:V=> (Y v).syntaxR (j i) (u i v) S
    rw [← (Tale.Congr.product K Finset.univ (B:=fun v:V=>X v i (u i v)) (A:=G) (fun v _=>(h v).2.2.2 _)).done K (s i)]
    refine Plan.slots_bill Y K (s i) (u i) (fun v=>Z v i) (fun v=>r v i) hξ (fun v=>(h v).2.1) (fun v=>(h v).2.2.1) hs (hd (k i) _ (fun v=> (he v).le)) hx hl (fun v=>(Nat.le_add_right ..).trans (he v|>.le)) (fun v=>(h v).1)
end
end YM.Frontier6.Road
