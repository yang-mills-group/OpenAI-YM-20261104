import YM.GapsContact.Earn.Buoys

/-!
# Units under relative log oscillation

No absolute horizon parameter. Instead allow lengths whose log expenses can
stretch arbitrary powers *or* be incomparable with the shell meter (small clock).
Need only that `dock r` paid as rate0 in that clock. This cannot simply be read
from Schedule.Gentle (may cost r^ε at transitions in that currency). Builds from
buoy resources to find any measuring scale and then using OnBudget of common construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson
open Labels Source Push Extra.Histories Bid Spec Ascent Power Stamps
open Trace Trace.Terrace Trace.Pilot Trace.Over MergeProof MergeProof.East
open Ward Climb OPE OPE.Log PhysicalNext.Repeat.Legato.Bandage
open scoped Topology BigOperators ContDiff InnerProductSpace Classical
variable {G:Gauge}{C:Family G}
variable {V X:Type*}{l:Filter V}{T g r s x y p: V→ℝ} {a b c:ℝ}
variable (hT:Tendsto T l atTop)
local notation "A!"=> C.path.levels
local notation "B!"=> C.path.levels.budget
local notation "α!"=> C.S.a
local notation "β!"=> C.path.levels.clock.hatBeta

/-- `Ridge`: expense of LogPoly in real length. No absolute power comparison. -/
structure Ridge (l:Filter V)(T g:V→ℝ):Prop where
   soon : ∀ᶠ i in l,g i∈ Ioc (0:ℝ) 1
   care : RateLE l T (fun i=>dock (g i)) 0
include hT
lemma rate_toll : RateLE l T (fun i=> T i) 0:= by
   have h:=OPE.Wallet.id hT; exact h.subpower hT -- inspect
include hT
-- utilities paying logarithms from even only relative RateLE of upper ratio (may be actually tiny)
omit hT in
lemma log_boost (h: RateLE l T x b) : ∀ᶠ i in l,1 ≤ x i → Real.log (x i) ≤ (b+1)*T i :=by
   filter_upwards [h (b+1) (lt_add_one b)] with i hi he using (Real.log_le_iff_le_exp (zero_lt_one.trans_le he)).2 ((Real.le_norm_self _).trans hi)
lemma Ridge.to (h:Ridge l T g) (hp:∀ᶠ i in l,r i∈Ioc 0 1) (hh:RateLE l T (fun i=>g i / r i) b) : Ridge l T r := by
   refine ⟨hp, (h.care.add ( ((RateLE.const |b+1| hT).mul (rate_toll hT)).mono (zero_add 0|>.le)) hT).transfer ?_⟩
   filter_upwards [h.soon,hp,hT.eventually_ge_atTop 0, log_boost hh] with i hi ht hv hQ
   refine le_trans ?_ (Real.le_norm_self _); rw [Real.norm_of_nonneg (zero_le_one.trans (dock_valid _ ht))]
   rcases le_total (g i) (r i) with h|h; · exact (dock_fold _ _ hi.1 h).trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) hv))
   have hh:dock (r i)= dock (g i)+Real.log (g i/r i):=by unfold dock LogV; rw [Real.log_inv,Real.log_inv,Real.log_div hi.1.ne' ht.1.ne']; ring
   exact hh.le.trans (add_le_add (le_refl _) ((hQ ((one_le_div ht.1).2 h)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hv)))
lemma Ridge.above (h:Ridge l T g)(he:∀ᶠ i in l, g i≤ r i)(hh:∀ᶠ i in l,r i≤1): Ridge l T r:=by
   have hp :∀ᶠ i in l,r i∈Ioc 0 1:=by filter_upwards [h.soon,he,hh] with i hi he ht using ⟨hi.1.trans_le he,ht⟩
   refine h.to hT hp (RateLE.absBound (A:=1) hT ?_)
   filter_upwards [h.soon,he,hp] with i hh hi hp; rw [Real.norm_of_nonneg (div_pos hh.1 hp.1).le]; exact (div_le_one hp.1).2 hi
lemma Ridge.clip (h:Ridge l T g): RateIs l T (fun i=>dock (g i)) 0:= RateIs.of_sandwich (RateIs.const hT one_pos) h.care (h.soon.mono fun _ hi=> dock_valid _ hi) (Eventually.of_forall fun _=> le_rfl) hT
lemma Ridge.motion (h:Ridge l T g) {w:ℝ}(hp:0 < w) :
    let r i:= g i * Real.exp (-w*T i); Ridge l T r∧ Tendsto r l trail ∧ (∀ᶠ i in l,r i ≤ g i) ∧ RateIs l T (fun i=>g i/r i) w :=by
   intro r; let f i:=Real.exp (w*T i); let y i:=Real.exp (-w*T i); have hy:∀ i,y i=(f i)⁻¹:=fun i=>by simp[y,f,Real.exp_neg]
   have hh(i):0< y i:=Real.exp_pos _; have hT':= (RateIs.exp (-w) hT).tends (neg_neg_of_pos hp) hT; change Tendsto y l _ at hT'
   have hf:∀ᶠ i in l, 0<r i ∧ r i≤g i ∧ r i≤ y i:=by
     filter_upwards [h.soon,hT'.eventually (ge_mem_nhds zero_lt_one)] with i hi he using ⟨mul_pos hi.1 (hh _),mul_le_of_le_one_right hi.1.le he,mul_le_of_le_one_left (hh _|>.le) hi.2⟩ -- shadow
   have h₁ := squeeze_zero' (hf.mono fun i hI=> hI.1.le) (hf.mono fun i hi=> hi.2.2) hT'
   have ht:RateIs l T (fun i=> g i / r i) w := (RateIs.exp w hT).congr (by filter_upwards [h.soon] with i hi; have he:f i≠0:= (Real.exp_pos _).ne'; have h₀:g i≠0:= hi.1.ne'; change f i=g i/(g i * y i); rw [hy]; field_simp)
   have hu:∀ᶠ i in l,r i ∈ Ioc 0 1:= by filter_upwards [h.soon,hf] with i hi ht using ⟨ht.1,ht.2.1.trans hi.2⟩
   exact ⟨h.to hT hu (ht.pays hT),tendsto_nhdsWithin_iff.mpr ⟨h₁,hf.mono fun i h=> h.1⟩,hf.mono fun i hi=> hi.2.1, ht⟩
omit hT
lemma Ridge.comp {φ:X→V}{f:Filter X}(h:Ridge l T g)(he:Tendsto φ f l):Ridge f (T∘φ) (g∘φ):=⟨he.eventually h.soon,h.care.comp he⟩
lemma Ridge.pos (h:Ridge l T g): ∀ᶠ i in l,0< g i:= h.soon.mono fun _ hi=>hi.1
lemma lake_line (d:ℕ) : Tendsto (fun r=> r*dock r^d) trail (𝓝 0):=by
   -- along r<1 and subspace
   have ht0:Tendsto dock trail atTop:=tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
   have hT:= ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp ht0).mul_const (Real.exp 8)
   rw [zero_mul] at hT; apply hT.congr'; filter_upwards [self_mem_nhdsWithin] with r hr
   simp only [Function.comp_def,mul_assoc, ← Real.exp_add]; rw [show -dock r+8=Real.log r from ?_,Real.exp_log (mem_Ioi.mp hr),mul_comm]; unfold dock LogV; rw [Real.log_inv]; ring

variable {𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book}
variable (F:Final C f S) (hG:G.Simple){H:(Climb.Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}
variable {j k m: V→ℕ}

structure Layer (C:Family G)(l:Filter V)(T:V→ℝ)(j:V→ℕ) : Prop where
   grows : Tendsto j l atTop
   stay : Ridge l T (C.S.a ∘ j)

include hT hG
lemma locate (hx: Bliss F 𝓛 Z H) (d:ℕ)(hr: Ridge l T r)(he:Tendsto r l trail): ∃ (j k: V→ℕ)(a:V→ℝ),Layer C l T j ∧ Layer C l T k ∧ RateIs l T (fun i=>α! (j i)/r i) 0 ∧ RateIs l T (fun i=>α! (k i)/r i) 0 ∧ RateIs l T a 0 ∧ ∀ᶠ i in l,Pool F 𝓛 (r i) (j i) (k i) d (a i):=by
   obtain ⟨t,h⟩:= every_pool F hG hx d
   let a:V→ℝ:= fun i=>dock (r i)^t
   let j(i:V):= if h:∃ j k,Pool F 𝓛 (r i) j k d (a i) then h.choose else 0
   let k(i:V):= if h:∃ k,Pool F 𝓛 (r i) (j i) k d (a i) then h.choose else 0
   have ht:∀ᶠ i in l, Pool F 𝓛 (r i) (j i) (k i) d (a i):=by
      filter_upwards [he.eventually h] with i hi
      change ∃ j k,Pool F 𝓛 (r i) j k d (a i) at hi; have hp:∃ k,Pool F 𝓛 (r i) (j i) k d (a i):=by unfold j; rw [dif_pos hi]; exact hi.choose_spec
      unfold k; rw [dif_pos hp]; exact hp.choose_spec
   let y:= α! ∘ j; let z:= α! ∘ k
   have hw: Tendsto z l (𝓝 0):= squeeze_zero' (Eventually.of_forall fun i=> C.S.a_pos (k i)|>.le) (ht.mono fun i hi=> hi.front.le) ((lake_line t).comp he)
   have hm : Tendsto k l atTop:= tendsto_atTop.mpr (fun i=>by filter_upwards [hw.eventually (ge_mem_nhds (C.S.a_pos i))] with x hx; exact C.S.strictAnti.le_iff_ge.mp hx)
   have h₁:Tendsto j l atTop:= tendsto_atTop_mono' l (ht.mono fun i hi=>hi.fore) hm
   have ha:RateIs l T a 0:= ((hr.clip hT).power t).swap (mul_zero _)
   have hi(i:V):0 < z i:=C.S.a_pos _
   have hd(i:V):0 < y i:=C.S.a_pos _
   have hv : ∀ᶠ i in l,(a i)⁻¹ ≤ y i/r i∧ y i ≤ z i∧ z i/r i≤a i:= by
      filter_upwards [ht,ha.pos,hr.pos] with i hi hh hu
      refine ⟨le_of_mul_le_mul_left ?_ hh,C.S.strictAnti.antitone hi.fore,(div_le_iff₀ hu).2 (hi.front.le.trans_eq (mul_comm ..))⟩; rw [mul_inv_cancel₀ hh.ne', ←mul_div_assoc]; exact (one_le_div hu).2 hi.breadth.le
   have hy : RateIs l T (fun i=> y i/r i) 0:= (ha.inv.swap (neg_zero)).of_sandwich (ha.pays hT) (hv.mono fun i hi=> hi.1) ((hv.and hr.pos).mono fun i hx=> (div_le_div_of_nonneg_right hx.1.2.1 hx.2.le).trans hx.1.2.2) hT
   have hz:= hy.of_sandwich (g:=fun i=>z i/r i) (ha.pays hT) ((hv.and hr.pos).mono fun i hx=> div_le_div_of_nonneg_right hx.1.2.1 hx.2.le) (hv.mono fun i hx=> hx.2.2) hT
   have h(i): C.S.a i ≤ 1:=by rw [← C.S.a_zero]; exact C.S.strictAnti.antitone (Nat.zero_le _)
   refine ⟨j,k,a,⟨h₁,?_⟩,⟨hm,?_⟩,hy,hz,ha,ht⟩
   · refine hr.to hT (Eventually.of_forall fun i=> ⟨C.S.a_pos (j i),h (j i)⟩) ((hy.inv.congr ?_).pays hT); exact Eventually.of_forall fun i=> inv_div ..
   refine hr.to hT (Eventually.of_forall fun i=> ⟨C.S.a_pos (k i),h (k i)⟩) ((hz.inv.congr ?_).pays hT); exact Eventually.of_forall fun i=> inv_div ..

omit hG hT
lemma Layer.direct (q: V→ℕ) (S:Schedule):∀ i,dock (S.a (q i))= 8+ S.scale (q i):=fun _=> rfl
lemma scale_le (P:Schedule)(k:ℕ):P.a k ≤ 1:=(P.strictAnti.antitone (Nat.zero_le k)|>.trans_eq P.a_zero)
lemma shiftOne (_:Layer C l T j) : ∀ᶠ i in l,1 ≤ α! (j i)/α! (j i+1):=Eventually.of_forall fun _=> (one_le_div (C.S.a_pos _)).2 (C.S.strictAnti.antitone (Nat.le_succ _)) -- no he?
include hG in
lemma bench_register (Q:Levels G)(θ:PostT Q): ∀ᶠ i in atTop,(Q.clock.J i:ℝ) ≤ Lyra Q i:=by
   filter_upwards [eventually_gt_atTop (0:ℕ)] with i hi
   cases i with
    | zero=> omega
    | succ i=> have ht := θ.cropK i; unfold ctl at ht; exact (Nat.cast_le.mpr (show Q.clock.J _ ≤ (Q.S.block i).val from le_trans (by omega) ht)).trans ((θ.bloom _).trans (lypos Q hG (Nat.le_succ _)))

include hT
lemma Layer.beta (h:Layer C l T j): RateIs l T (β! ∘ j) 0:=by
   refine RateIs.of_sandwich (RateIs.const hT one_pos) (f':=β! ∘ j) ?_ (Eventually.of_forall fun i=> ((A!).fits.delayed _).le) (Eventually.of_forall fun _=> le_rfl) hT
   have ht: RateLE l T (fun i=>C.S.scale (j i)) 0:= ((h.stay.care).sub (RateLE.const (8:ℝ) hT) hT).congr (Eventually.of_forall fun i=> by change 8+C.S.scale (j i)-8=_; ring)
   refine RateLE.add (F:=fun _=> (A!).clock.bar) (F':=fun i=> G.slopeConstant * C.S.scale (j i)) (RateLE.const _ hT) (((RateLE.const (G.slopeConstant) hT).mul ht).mono (by linarith only)) hT -- rfl?

lemma Layer.lyra (h:Layer C l T j) : RateLE l T (Lyra A! ∘ j) 0:=
   (h.beta hT|>.pays hT).transfer (Eventually.of_forall fun i=>by simp only [Function.comp_apply]; rw [Real.norm_of_nonneg (lira ..|>.le),Real.norm_of_nonneg (bell ..|>.le)]; exact Real.log_le_self (bell ..|>.le))

variable {W r' D} (L:LogPackage C W r' D)
include L
lemma Layer.jump (h:Layer C l T j) : RateIs l T (fun i=> α! (j i)/α! (j i+1)) 0:=by
   refine RateIs.of_sandwich (RateIs.const hT one_pos) ((h.beta hT).pays hT) (shiftOne h) ?_ hT
   refine Eventually.of_forall fun i=>?_ ; rw [C.S.a_step]; rw [show α! (j i)/(α! (j i)/(↑(C.S.block (j i)).val:ℝ))=(C.S.block (j i)).val from (by field_simp [(C.S.a_pos _).ne'])]; exact L.money.mesh _ -- unfold
lemma Layer.next (h:Layer C l T j): Layer C l T (fun i=>j i+1):= ⟨tendsto_atTop_mono (fun i=> Nat.le_succ (j i)) h.grows,h.stay.to hT (Eventually.of_forall fun _=>⟨C.S.a_pos _, scale_le C.S _⟩) ((h.jump hT L).pays hT)⟩

variable (h:Layer C l T j) (θ:PostT C.path.levels) (P:Stock.Tabs C.path.levels)
include h
omit L
lemma Layer.cover : RateLE l T (fun i=> ((B! (j i)).B:ℝ)) 0:= (( (Layer.lyra hT h).pow 2 hT).mono (by norm_num : (↑(2:ℕ):ℝ)*0 ≤ 0)|>.add (RateLE.const 1 hT) hT)|>.of_norm_le (Eventually.of_forall fun i=>by rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact Bcharged ..)
include hG θ
lemma Layer.basinJump : RateIs l T (fun i=> α! (j i) / α! (basin A! P (j i))) 0:= by
   refine RateIs.of_sandwich (RateIs.const hT one_pos) (f':=fun i=> Lyra A! (j i)^6) (((Layer.lyra hT h).pow 6 hT).mono (by norm_num)) (Eventually.of_forall fun i=> (one_le_div (C.S.a_pos _)).2 (C.S.strictAnti.antitone (unwinds ..))) ?_ hT; filter_upwards [h.grows.eventually (Bgap A! hG θ P)] with i hi using hi.1
lemma Layer.basinLevel : Layer C l T (basin A! P ∘ j) := ⟨(bondB A! P).comp h.grows,h.stay.to hT (Eventually.of_forall fun _=>⟨C.S.a_pos _,scale_le C.S _⟩) ((Layer.basinJump hT hG h θ P).pays hT)⟩

omit θ hG
open PhysicalNext.Repeat.Legato.Bandage
local notation "τ'"=> PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels
local notation "η'"=> near C.path.levels
local notation "δ'"=> renal C.path.levels
lemma Layer.fly (d:ℕ) : RateIs l T (fun i=> τ' d (j i)) 0:= (((h.beta hT).power (MergeProof.winter G d)).inv).swap (by simp)
include L
lemma Layer.renalT : RateIs l T (fun i=> δ' (j i)) 0:=by simp_rw [price_paid]; exact ((((h.next hT L).beta hT).power 2).inv).swap (by norm_num)
lemma Layer.nearT : RateIs l T (fun i=> η' (j i)) 0:= ((h.next hT L).beta hT|>.inv)|>.swap (by norm_num)
lemma Layer.columns : RateIs l T (fun i=>1+(C.path.levels.params (j i)).columns) 0:=by
   refine RateIs.of_sandwich (RateIs.const hT one_pos) ((RateLE.const 1 hT).add (F':= β! ∘ j) ((h.beta hT).pays hT) hT) ?_ ?_ hT
   · exact Eventually.of_forall fun _=> le_add_of_nonneg_right (zero_le_one.trans ((A!).params _).columns_ge)
   exact Eventually.of_forall fun i=> add_le_add_right (L.money.present _) _
open MergeProof.Ribbons.ManyCopies
set_option maxRecDepth 5000 in
lemma Layer.tuition (B:ℕ)(hb:0<B) : RateIs l T (fun i=> solvency L B (j i)) 0 := by
   let p i:=short L (j i)+2; let a(i):= (A!).clock.hatBeta (j i+1); have ha : RateIs l T a 0:=(h.next hT L).beta hT
   let f(i):= Real.exp ((100+(1/2:ℝ))*p i)
   have hf : RateIs l T f 0:=by
       refine RateIs.of_sandwich (RateIs.const hT one_pos) (((RateLE.const (Real.exp ((100+(1/2:ℝ))*11)) hT).mul (furtherT ha)).mono (by simp)) (Eventually.of_forall fun _=>Real.one_le_exp (mul_nonneg (by norm_num) (Nat.cast_nonneg _))) ?_ hT -- furtherT local
       refine Eventually.of_forall fun i=>?_; let x:= Real.log (a i); have hx:(p i:ℝ) ≤ 256*x+11:=by unfold p; push_cast; linarith only [show (short L (j i):ℝ) ≤ 256*x+9 from short_upper L (j i)]
       refine le_trans (b:=Real.exp ((100+(1/2:ℝ))*11+(25728:ℝ)*x)) (Real.exp_monotone (by linarith only [hx])) (le_of_eq ?_); rw [Real.exp_add, show (25728:ℝ)=↑(25728:ℕ) from rfl, Real.exp_nat_mul,Real.exp_log (bell ..)]
   simp_rw [solvency,license,show ∀ i,(A!|>.budget i).supportExponent=(100:ℝ) from L.support]; let g:= h.renalT hT L; exact ((((g.div (RateIs.const hT (Nat.cast_pos.mpr hb))).mul g).div hf).mul g).swap (by simp)
where furtherT {x:V→ℝ}(hr:RateIs l T x 0) : RateLE l T (fun i=> x i^(25728:ℕ)) 0:= ((hr.power _).swap (by simp)).pays hT

omit L h
lemma tower_earlier (hx: RateIs l T (fun i=>α! (j i)/α! (k i)) a) (ha: 0<a) : ∀ᶠ i in l,j i<k i:=by
   filter_upwards [hx.overtakes (RateLE.const (1:ℝ) hT) hT ha] with i hi using C.S.strictAnti.lt_iff_gt.mp ((one_lt_div (C.S.a_pos _)).1 hi)
omit hT in
lemma tower_attach (hp: RateIs l T (fun i=>α! (k i)/α! (m i)) a)(hx: RateIs l T (fun i=>α! (j i)/α! (k i)) b): RateIs l T (fun i=>α! (j i)/α! (m i)) (b+a):=by
   apply (hx.mul hp).congr; refine Eventually.of_forall fun i=>?_ ; field_simp [(C.S.a_pos _).ne']
omit hT
lemma relation_mul (hr: ∀ᶠ i in l,r i ≠ 0)(hx : RateIs l T (fun i=> x i/r i) a)(hp:RateIs l T (fun i=>r i/y i) b): RateIs l T (fun i=>x i/y i) (a+b):= by refine (hx.mul hp).congr ?_; filter_upwards [hr] with i hi; field_simp
lemma relation_inv (hr: RateIs l T (fun i=> x i/y i) a) : RateIs l T (fun i=>y i/x i) (-a):= hr.inv.congr (Eventually.of_forall fun _=> inv_div ..)
end YM.GapsContact.Seams
