import YM.X.Fill.Travels
/-!
# Scalar ℂ support motion & transfer of ∆^n with all roots.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Friend
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension LatticePT MeasureTheory Metric Filter Set Function Asymptotics Reed Braid Fielding Haze Clove Interval CellsInt Shelf Size Print Beamer
open scoped Topology ContDiff Classical BigOperators
variable {V:Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {q:ℕ+} (hq:1<q.val){k m:ℕ}{a b n : ℤ}{R r:ℝ}
abbrev Mint:= Cover→₀ℂ
def cane (χ:Lane)(f:Cover→ℂ): Mint:=Finsupp.ofSupportFinite (fun x=> χ x • f x) ((Finset.finite_toSet χ.support).subset fun x h=> by rw [Finset.mem_coe,Finsupp.mem_support_iff]; exact fun he=> h (show χ x • f x=0 from by rw [he,zero_smul])) -- name collides
lemma cane_at (χ:Lane)(f:Cover→ℂ)(x): cane χ f x=χ x • f x:=rfl
def palm (p:ℕ→ Mint): Mist ℂ :=fun i z=> p i z
def notZero (T:ℕ→Mint)(f:Mist ℂ)(k:ℕ): ℂ:= Finsupp.linearCombination ℂ (f k) (T k)
def ford (χ:ℕ→ Mint)(x:Cover):ℕ→ Mint:= fun k=> (χ k).equivMapDomain (Equiv.addRight (-x))
variable {p:ℕ→Mint} (l:List Axis) (v:Cover)
lemma palm_ford (t:ℕ→Mint): palm (ford t v)= alter v (palm t):= by ext1 i; ext1 z; unfold palm ford; rw [Finsupp.equivMapDomain_apply]; apply congr_arg; exact sub_neg_eq_add z v
lemma ford_at (t:ℕ→ Mint)(f:Mist ℂ) : notZero (ford t (-v)) f= notZero t (alter v f):= by ext1 i; unfold ford notZero; simp only [neg_neg,Finsupp.equivMapDomain_eq_mapDomain,Finsupp.linearCombination_mapDomain];rfl
lemma inversum (B:Mist ℂ): Frugal (fun z=>p k z * B k z) (p k).support:= by intro i h; rw [Finset.mem_coe,Finsupp.mem_support_iff]; exact fun he=> h (show p k i*B k i=0 from by rw [he,zero_mul])
include hq
lemma support_ford (h: Starboard q R (palm p))(he: R<r)(hx: R≥0) : Starboard q r (palm (ford p v)):= by
   rw [palm_ford]; filter_upwards [h,gate_shift hq _ _ he hx (-v)] with i hi h' z hz; replace hp:= h' (z+v) (hi _ hz); simpa using hp
lemma increase_support (h: Starboard q R (palm p))(he:R≤r): Starboard q r (palm p):= h.mono (fun i hi z hz=> (hi z hz).trans (Nat.floor_le_floor (mul_le_mul_of_nonneg_left he (amp_pos q i|>.le))))
def retire (χ:ℕ→Mint)(i: Axis):ℕ→Mint := fun k=>χ k - ford χ (-step i) k
lemma retire_point (p:ℕ→Mint)(z:Cover)(i:Axis)(k:ℕ): retire p i k z=p k z-p k (z+ -step i):= by rw [retire,Finsupp.sub_apply]; exact congr_arg (p k z - ·) (congr_fun (congr_fun (palm_ford (-step i) p) k) z) -- includes hq undesired
lemma palm_retire (χ:ℕ→Mint)(i:Axis): palm (retire χ i)= alter (-step i) (forward i (palm χ)) := by ext1 k;ext1 z;unfold palm; rw [retire_point hq]; change _= χ k (z + -step i+step i)-_; rw [neg_add_cancel_right]
lemma retreat_support (p:ℕ→Mint)(i:Axis)(h:Starboard q R (palm p))(he: R<r)(ht:R≥0): Starboard q r (palm (retire p i)):= by
   filter_upwards [increase_support hq h he.le,support_ford (v:=-step i) hq h he ht] with k hp hi z hz; by_contra hh; have he:p k z=0:=not_not.mp fun h'=>hh (hp z h'); have hv:ford p (-step i) k z=0:=not_not.mp fun h'=>hh (hi z h'); apply hz; unfold palm retire;rw [Finsupp.sub_apply,he,hv,sub_zero]
-- all numeric tables for Green as measured at mark 0
local notation "L"=>(atTop:Filter ℕ)
def squall (q:ℕ+)(B:GridF): Mist ℂ:= fun t z=> ((B (side q t) 0 z):ℂ)
lemma shelved (i: Axis) : notZero p (squall q (graphK (i::l) v))= notZero (retire p i) (squall q (graphK l (v+step i))):= by
   let B:=squall q (graphK l (v+step i)); have he(k:ℕ)(z:Cover): squall q (graphK (i::l) v) k z=B k z-B k (z+step i):= by
       unfold squall; let d:=side q k; unfold B squall; push_cast; rw [← Complex.ofReal_sub]; apply congr_arg; have h:= Print.slopeY (n:=d) 0 z (v+step i) l i; rw [add_sub_cancel_right] at h; change graphK (i::l) v d 0 z=_; linarith only [h]
   funext k; unfold notZero retire; let f k := (B k:Cover→ℂ); rw [show squall q _ k=f k-alter (step i) B k from funext (he k),map_sub]
   have ht:= congr_fun (ford_at (step i) p B) k; unfold notZero at ht; rw [ht]; simp [Finsupp.linearCombination_apply,Finsupp.sum,f,B,mul_sub,Finset.sum_sub_distrib]
lemma stargem (S:Starboard q R (palm p))(he:0≤ R)(hr:R<r)(h:Chase q r ((4:ℤ)-(2+l.length)) (palm p)): Released (notZero p (squall q (graphK l v))):= by
   induction l generalizing R v p with
   | nil=>
       let x:= squall q (graphK [] v); have hx:= Visa.com (Haze.rooted_bird hq he (B:=graphK [] v) (k:=0) (graph_bird [] v rfl))
       have ht: Visa q R 1 (-3) (palm p*x):= by apply Visa.stretch hq (Visa.mulC (h.visa he hr) hx) he <;> (first|omega|norm_num)
       have h₁: Starboard q R (palm p*x):= S.mono (fun i hi z hz=> hi z (left_ne_zero_of_mul (show _ *x i z≠0 from hz))) -- name
       exact dom_release (w:=fun i=> (p i).support) hq he ht (Eventually.of_forall fun i=> inversum x) h₁
   | cons i l IH=>
       obtain ⟨T,hT,ht⟩:=exists_between hr; rw [shelved hq l v]; apply IH _ (retreat_support hq _ _ S hT he) (by linarith) ht; rw [palm_retire hq]; have hh:= (h.step i).alts hq (-step i); convert hh using 1; simp; ring -- cast
end YM.PositionX.Friend
