import YM.RG17.Stow
/-!
# Real non-Taylor erase rate in fine coupling

 Accept any fixed polynomial number of adjusted sites in BudgetPoint.B; no
 delay besides the ORIGINAL physical C. Uniform all m < N. Precision loss
 here is deliberately overkill and only concerns THIS insertion of the already
 rare arity side estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Lattice Wilson RG Pressure Shoot Supply
open PhysicalNext.Repeat.Legato Pert.Asymptotics Push.AbsoluteSums Footprint
open AnalyticBridge VerifiedReset Collection
open scoped Classical Topology Matrix.Norms.Frobenius
set_option quotPrecheck false
variable {G:Gauge}(R:Run G) {m p N:ℕ} (h:G.Simple)
local notation "C"=> R.family
local notation "g"=> regulatorRun R.family
local notation "H"=> R.family.path.levels
local notation "ζ"=> R.family.path
local notation "η"=> R.family.path.levels.clock.hatBeta

theorem hasWoodsP (m p:ℕ) : Nonempty (woodsP R m p):= Tree.select ((H).clock.op m p).ratio ((H).clock.op m p).patch.odd_side

include h
private lemma stowG (hm:m<N) :
    let k:=g N p (m+1)
    0<k ∧ k ≤ Real.sqrt 2 ∧ ((H).budget m).B*k^4 ≤ (8:ℝ):=by
    intro k
    let x:=(η m); let y:=η (m+1); let b:=(ζ).β N p (m+1)
    have ht:y / 2≤ b:= (R.makes.wilson.represents N p (m+1) hm).band.1
    have hh:1 < x := (H).fits.delayed m
    have hx:x ≤ y := by
        unfold x y Calendar.hatBeta; gcongr
        · exact (Gauge.slopeConstant_pos h).le
        let S:=(ζ).S; change S.scale m ≤ S.scale (m+1); rw [S.scale_succ]; linarith only [Real.log_nonneg (show 1≤ ((S.block m).val:ℝ) from Nat.one_le_cast.mpr (S.block m).pos)]
    have hy:0<b :=by linarith only [ht,hx,hh]
    have hD : 0<k:= show 0 < (Real.sqrt b)⁻¹ from inv_pos.mpr (Real.sqrt_pos.mpr hy)
    refine ⟨hD, show (Real.sqrt b)⁻¹ ≤ _ from ?_,?_⟩
    · rw [inv_le_comm₀ (Real.sqrt_pos.mpr hy) (by positivity), ← Real.sqrt_inv]; apply Real.sqrt_le_sqrt; linarith only [ht,hx,hh]
    have he:((H).budget m).B ≤ Nat.ceil ((Real.log x)^2):= Nat.le_refl _
    have hv:(((H).budget m).B:ℝ) ≤ 8*b^2:=by
        apply le_trans (Nat.cast_le.mpr he) ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_)
        have hi:((Real.log x)^2 :ℝ)≤ x^2:= pow_le_pow_left₀ (Real.log_nonneg hh.le) (by linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans hh)]) _
        have hq:x^2 ≤ (2*b)^2:=pow_le_pow_left₀ (by linarith) (by linarith only [hx,ht]) _
        nlinarith only [hi,hq,one_le_pow₀ (n:=2) hh.le]
    apply (mul_le_mul_of_nonneg_right hv (pow_nonneg hD.le _)).trans
    change _*(Real.sqrt b)⁻¹^4 ≤ _; rw [inv_pow,show Real.sqrt b^4=b^2 by rw [show 4=2*2 from rfl,pow_mul,Real.sq_sqrt hy.le],mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hy.ne'),mul_one]

def preArity (d w:ℕ):=d+4*(4+w)
private def component := 24*Real.exp 1*(1-Real.exp (-1))⁻¹
omit h in
private lemma edit_simple (p:BudgetPoint){u:ℝ}(hu:0≤u)(s:ℕ): editsFee p u s ≤ 2*(s*(u*(13*p.B)^4*component)):=by
    have hp:Real.exp (-1)<1:= Real.exp_lt_one_iff.mpr (by norm_num)
    have hh:0 ≤ component:= by 
        unfold component; have h:0≤1-Real.exp (-1):=by linarith
        positivity
    have hB : (((spread 1 (4*p.B+2)):ℕ):ℝ) ≤ (13*(p.B:ℝ))^4:=by
        simp only [Footprint.spread,one_mul, Animals.ballCost, Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]; apply pow_le_pow_left₀ (by positivity); linarith only [show 1≤(p.B:ℝ) from Nat.one_le_cast.mpr p.B_pos]
    unfold editsFee; gcongr 2*(_*?_) -- payment single
    have hP: payment 1 (4*p.B+2) 0 1 1 u (p.supportExponent+1) 0 = u*(spread 1 (4*p.B+2):ℝ)*component:=by
        unfold payment degreeIncome component; norm_num [Nat.factorial]; ring -- norm of exp?
    rw [hP]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hu) hh

/-- Applicable simultaneously on all actually priced insertion variants. -/
theorem earlyFare (d w:ℕ) {b c:ℝ}(hb:0 ≤ b)(hc:0 ≤ c) :∃ t :ℝ,0≤ t ∧ ∀ N p m:ℕ, m<N →∀ s:ℕ, (s:ℝ) ≤ b*((R.family.path.levels.budget m).B:ℝ)^w →
    Real.exp (pieces17 R N m p (preArity d w) s c)-1 ≤ t * regulatorRun R.family N p (m+1)^d:=by
    let A:= 2*b*c*13^4*component*8^(4+w)
    have hp:Real.exp (-1) < 1:= Real.exp_lt_one_iff.mpr (by norm_num)
    have hc':0 ≤ component:= by 
        unfold component; have h:0≤1-Real.exp (-1):=by linarith
        positivity
    let t:= Real.exp (A*Real.sqrt 2^d)*A
    have hA:0 ≤ A:=by unfold A; positivity
    have ht :0 ≤ t:=by unfold t; positivity
    refine ⟨t,ht,fun N p m hm s hs=>?_⟩
    let k:= regulatorRun R.family N p (m+1); let V:= A*k^d
    let P:= R.family.path.levels.budget m; let B:ℝ:=P.B
    have hz:0≤B:= by unfold B; positivity
    obtain ⟨hg,hK,hG⟩:= stowG (p:=p) R h hm
    have h₀:0< k:=hg
    have hv: 0≤V:=by unfold V; positivity
    have hT: pieces17 R N m p (preArity d w) s c ≤ V:=by
      change editsFee P (c*k^_) s ≤ V
      refine le_trans (edit_simple P (by positivity) _) ?_
      apply le_trans (b:=2*(b*B^w)*(c*k^(preArity d w)*(13*B)^4*component))
      · rw [mul_assoc 2]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (by positivity)) (by norm_num)
      unfold preArity V A
      rw [show 2*(b*B^w)*(c*k^(d+4*(4+w))*(13*B)^4*component)= (2*b*c*13^4*component)*(B*k^4)^(4+w)*k^d by ring] -- rewrite lhs pieces
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hG _) (by positivity)) (by positivity)
    apply (sub_le_sub_right (Real.exp_monotone hT) _).trans
    have hx:= mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-V)) (Real.exp_pos V).le
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at hx
    apply le_trans (b:=Real.exp V * V) (by linarith only [hx]); unfold t; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le hK _) hA)) hv

open RG01 RG01.Kernel

-- Any stopsGuide. `c` here packages quotation stamp rate, `t` extra local costs. K = arbitrary supports fitting quote. Single-step denominator substitution error.
theorem earnedHere (d w:ℕ) {b:ℝ}(hb:0 ≤ b) :∃ c t:ℝ,0 ≤ c ∧0 ≤ t ∧∀ (N p m:ℕ),m<N→∀ (L:BeaconP R N p m)(_hL:stopsGuide R L)(O:woodsP R m p), discards R L O (preArity d w) c ∧
    ∀ V V':Config G ((C).side m p), ∀ ε: Edge (Site ((C).side m p))→ℝ,(∀ i, ε i=0→ V' i=V i)→∀ K:Support ((C).side m p), Agrees (K:Set (Site ((C).side m p)))ᶜ V V' → ((halo 8 K).card:ℝ) ≤ b * ((R.family.path.levels.budget m).B:ℝ)^w →∀ (F : (R.family.path.levels.clock.op m p).Choices → Config G ((C).side (m+1) p)→ℂ)(a:ℝ), Kernel.Bounded (Wilson.prior ..) F a →
     ‖conditional (C).path N m p V' F - collectible R L O (preArity d w) V ε F V'‖ ≤ a*(t* regulatorRun R.family N p (m+1)^d):=by
    obtain ⟨c,hc,hV⟩:= hikes R h (preArity d w)
    obtain ⟨t,ht,hT⟩:= earlyFare R h d w hb hc
    refine ⟨c,t,hc,ht,fun N p m hm L hL O=> ⟨hV m N hm p L O hL,fun V V' ε h K hK hS F a hf=> ?_⟩⟩
    exact (denomination (hV m N hm p L O hL) hm _ _ _ h K hK F hf).trans (mul_le_mul_of_nonneg_left (hT N p m hm _ hS) ((norm_nonneg _).trans ((Kernel.actual N R.family.path R.makes.wilson V' hm).price hf)))
end YM.RG17
