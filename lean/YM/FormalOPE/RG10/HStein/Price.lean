import YM.FormalOPE.RG10.HStein.Opt
/-!
# Tier weights for a Stein transfer
 Generalized moment currency, unifying root exponential and polynomial moment. Use
 only in compatible units chosen in advance, one family with α scalar uniform. Price sums
 are absolute across monomials (complex coefficient norm); no per-element data coming from actual
 $MarkedSeries` reader. Lens strives to charge farthest from union of profiles or from one
 center (addresses tested first). No geometry compared with torus images until picked. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open Function PowerSeries Finset
open Route
open scoped Topology BigOperators Classical
-- open two OK? open Route doesn't open Multi with select syntax? inspect
structure Tier where
 value : ℝ→ℝ
 blind : value 0=1
 near {x y:ℝ} : 0 ≤ x → x ≤ y → value x ≤ value y
 toll {x y:ℝ} : 0 ≤ x → 0 ≤ y → value (x+y) ≤ value x * value y
variable (F G: Tier)

namespace Tier
lemma grade {x:ℝ}(h:0≤x) : 1 ≤ F.value x:= F.blind ▸ F.near (by rfl) h -- inspect
lemma cp {x:ℝ}(h:0≤x):0≤F.value x:= zero_le_one.trans (F.grade h)

def pol (n:ℕ) : Tier := ⟨fun x=>tip x n, tip_zero _, fun hx hy => tip_mono hy hx _, fun hx hy=> tip_add hx hy _⟩

def fade (σ:ℝ) (h:0≤σ) : Tier where
 value x:= Real.exp (σ*x)
 blind:= by simp
 near hx hy:= Real.exp_monotone (mul_le_mul_of_nonneg_left hy h)
 toll hx hy:= by rw [mul_add,Real.exp_add]

def repeatAfter : Tier where
 value x:= F.value x * G.value x
 blind:= by rw [F.blind,G.blind,mul_one]
 near hx hy:= mul_le_mul (F.near hx hy) (G.near hx hy) (G.cp hx) (F.cp (hx.trans hy))
 toll hx hy:= (mul_le_mul (F.toll hx hy) (G.toll hx hy) (G.cp (add_nonneg hx hy)) (mul_nonneg (F.cp hx) (F.cp hy))).trans (le_of_eq (by ring))

def expMoment (σ : ℝ) (h:0≤σ)(n:ℕ) := (pol n).repeatAfter (fade σ h)
-- transport on packet letters
variable {I : Type} {T:Type*} {K: Tape T} (p : I → ℝ) (h: 0≤p)

def face (c:Letters I) := F.value (along p c.support)
def dep (x : I) := F.value (p x)-1
include h in
lemma dep_sign (a:I):0≤F.dep p a := by unfold dep; exact sub_nonneg.mpr (F.grade (h a)) -- include

def valueOf (P: Packet I):ℝ := worth (F.dep p) 1 P
def gain (P:Channel I)(k:ℕ):= mag (F.dep p) 1 k P
def free : Tier := pol 0 -- inspect implicit F unused no include
include h in
lemma face_eq (c : Letters I) : F.face p c= fare (F.dep p) 1 c:= by
 unfold face fare tip; rw [pow_one]
 let f:=F.dep p; change F.value (along p c.support)=1+along f c.support
 by_cases he:c.support.Nonempty
 · obtain ⟨a,ha,ht⟩:=exists_mem_eq_sup' he p
   have hn : along p c.support=p a:= by rw [along,dif_pos he,ht]
   have hv : along f c.support=f a:= le_antisymm (along_le _ _ (F.dep_sign p h a) (fun b hb=>sub_le_sub_right (F.near (h b) ((le_along hb p).trans hn.le)) _)) (le_along ha f)
   unfold f dep at *; rw [hn,hv]; ring
 · rw [along,dif_neg he,along,dif_neg he, F.blind]; ring

variable {H:Type*} (P Q:Packet I) (c c₁ : Letters I)
omit h in
lemma silent : F.face p (0: Letters I)=1:= by simp [face,F.blind]
-- costs
include h
lemma ready : 1 ≤ F.face p c := F.grade (along_nn h _)
lemma bright : 0 ≤ F.face p c:= F.cp (along_nn h _)
lemma lower : 0 ≤ F.valueOf p P:= worth_nonneg _ (F.dep_sign p h) _ P
lemma capital : F.valueOf p P = ∑ m∈ P.support,F.face p m*‖MvPolynomial.coeff m P‖ :=by
 unfold valueOf worth; simp_rw [F.face_eq p h]
lemma money (b:ℂ): F.valueOf p (MvPolynomial.monomial c b)=F.face p c*‖b‖:= by unfold valueOf; rw [worth_monomial,face_eq F p h]
lemma grows (hh : c≤c₁) : F.face p c ≤ F.face p c₁:= F.near (along_nn h _) (mono_along (Finsupp.support_mono hh) p p (fun _ _=> le_rfl) h)
omit h
lemma level (a:I) : F.face p (Finsupp.single a 1)=F.value (p a):= by simp [face]
include h
lemma degree (a:I)(ha:a ∈ c.support):F.value (p a)≤F.face p c:= F.near (h a) (le_along ha p)
lemma max_cost : F.face p (c+c₁) ≤ max (F.face p c) (F.face p c₁):= by
 rcases le_total (along p c.support) (along p c₁.support) with ha|ha
 · exact le_trans (F.near (along_nn h _) ((along_add p h c c₁).trans (Eq.le (max_eq_right ha)))) (le_max_right ..) -- inspect
 exact le_trans (F.near (along_nn h _) ((along_add p h c c₁).trans (Eq.le (max_eq_left ha)))) (le_max_left ..)
omit h in
lemma coins (b:ℂ): F.valueOf p (b • P) = ‖b‖ * F.valueOf p P:= worth_smul .. -- omit
lemma plus : F.valueOf p (P+Q) ≤ F.valueOf p P + F.valueOf p Q := worth_add _ (F.dep_sign p h) _ _ _
lemma many (g:H→Packet I)(A:Finset H): F.valueOf p (∑ i∈A,g i)≤∑ i∈A,F.valueOf p (g i):= worth_sum _ (F.dep_sign p h) _ _ _
omit h
lemma zero : F.valueOf p 0=0:= worth_empty ..
lemma unit : F.valueOf p 1=1:= worth_one ..
lemma value_free (p:I→ℝ)(hh:0 ≤ p) : free.valueOf p P = worth p 0 P:= by rw [capital free _ hh]; rfl -- need simp
lemma ordinary (u:ℕ) (H:0≤p): (pol u).valueOf p P=worth p u P:= by rw [capital (pol u) _ H]; rfl
@[simp] lemma free_stamp (a:ℝ): free.value a=1:= pow_zero _
@[simp] lemma flat : free.face p c=1 := free_stamp _
include h
lemma multiplies : F.valueOf p (P*Q) ≤ F.valueOf p P * F.valueOf p Q:= worth_mul _ (F.dep_sign p h) _ P Q
/-- A single port bearing ALL of the resulting position cost on a product. Crucially the
 remaining ports pay only their unweighted sum. -/
theorem twice : F.valueOf p (P*Q) ≤ free.valueOf p P * F.valueOf p Q + F.valueOf p P * free.valueOf p Q:= by
 rw [MvPolynomial.mul_def]; simp_rw [MvPolynomial.sum_def]; apply (F.many p h _ _).trans
 rw [capital free _ h, F.capital p h,F.capital p h,capital free _ h, sum_mul_sum,sum_mul_sum, ←sum_add_distrib]; apply sum_le_sum; intro i _
 apply (F.many p h _ _).trans; rw [← sum_add_distrib]; apply sum_le_sum; intro j _;
 rw [money F p h,norm_mul,flat,flat]
 have hx := le_trans (max_cost F p h i j) (max_le (le_add_of_nonneg_left (F.bright p h j)) (le_add_of_nonneg_right (F.bright p h i))) -- order f? j+i? inspect
 apply le_trans (mul_le_mul_of_nonneg_right hx (by positivity)); exact le_of_eq (by ring)
end Tier
end YM.FormalOPE.RG10.HStein
