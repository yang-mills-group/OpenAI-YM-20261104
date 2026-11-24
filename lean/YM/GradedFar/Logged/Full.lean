import YM.GradedFar.Logged.VAC
import YM.GradedFar.Logged.Weak
/-! The entire ordinary near-minus-child reading (extends `Integration/WilsonPublicForkOrdinary`) against the far field
on the original continuum table.  Both root subtractions and the whole
projected jump use the same viewer and all-power raw prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Full
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open Tree Tree.Node
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {I J:Type} [Fintype I][Fintype J] {P:Prescription F.sector.derivatives}
local notation "sites" => Tree.position
local notation "nearSet" => Tree.near I J
local notation "tree" => Tree.frame I J
local notation "bare" => Stage.bare
local notation "farSet" => Tree.outer I J
def demand (v:Viewers F)(X:Node I J→E4)(b:Finset (Node I J))(p:Node I J→C.book.Token):ℂ:=
  whole (spectator F v) b X p (bare:Fin 0→E4) bare

theorem main (simple:G.Simple) (bank:LogTrace F P)(p:Node I J→C.book.Token)(h:ℕ)
    {M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(b:ℝ)(K:ℕ),0≤b ∧ ∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(z:J→E4)(o:E4),0<r → r≤t → (∀i,‖x i‖≤M) → (∀i,‖z i‖≤M) → (∀i,2*δ≤‖z i‖) → (∀i j,i≠j→δ≤‖x i-x j‖) → r*M≤t*δ → (∀i j,i≠j→δ≤‖z i-z j‖) → ∀v:Viewers F,
      let X:=sites r t x z o
      mass p r t*‖demand F v X (tree).leaves p-
          ∑u∈bands F.sector.derivatives h,coalesce P nearSet X p child u*
              demand F v X farSet (update p child (P.letter u))‖ ≤
        b*(badge t*badge r)^K*(t+(r/t)^(h+1)):=by
  let A:=↥(bands F.sector.derivatives 0)
  let B:=↥(bands F.sector.derivatives h)
  let pay (a:Mode F.sector.derivatives):ℂ:=
    VAC.value F P a
  choose ih earns using fun u:B=>Stage.inner F bank p u.1 mn dp
  choose oh owes using fun u:B=>Stage.outside F bank p u.1 mn dp
  choose ah heard using fun a:A=>Stage.joint F bank p h a.1
    (Nat.eq_zero_of_le_zero ((full_bands ..).mp a.2)) mn dp
  obtain ⟨k,allpay⟩:=Stage.full F bank p mn dp
  obtain ⟨r₀,pos,inside⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp (Filter.eventually_all.mpr earns)
  let K:=k+(∑i,ih i)+(∑i,oh i)+(∑j,ah j)
  let b:ℝ:=1+(∑a∈bands F.sector.derivatives 0,‖pay a‖)+(bands F.sector.derivatives h).card
  refine ⟨b,K,by dsimp [b];positivity,?_⟩
  have late : (∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ min 1 r₀) :=
    (ge_mem_nhds (lt_min zero_lt_one pos)).filter_mono nhdsWithin_le_nhds
  filter_upwards [late,allpay,Filter.eventually_all.mpr owes,
    Filter.eventually_all.mpr heard] with t h₀ hf ho ha
  intro r x z o hr rt hx hz fz sep room sep2 v
  dsimp only
  have ht:=hr.trans_le rt
  have nearRates:=inside (show r∈Ioc (0:ℝ) r₀ from ⟨hr,rt.trans (le_min_iff.mp h₀).2⟩)
  have t1:1≤badge t:=by
    unfold badge run;linarith [Real.log_nonpos ht.le (le_min_iff.mp h₀).1]
  have r1:1≤badge r:=by
    unfold badge run;linarith [Real.log_nonpos hr.le (rt.trans (le_min_iff.mp h₀).1)]
  let L:=badge t*badge r
  have L1:1≤L:=one_le_mul_of_one_le_of_one_le t1 r1
  have kK:k≤K:=by dsimp [K];omega
  have eqpos:0 ≤ mass p r t:=mul_nonneg (pow_nonneg hr.le _) (pow_nonneg ht.le _)
  let X:=sites r t x z o
  let c (u:Mode F.sector.derivatives):=coalesce P nearSet X p child u
  let pp (u:Mode F.sector.derivatives):=update p child (P.letter u)
  let q (u a:Mode F.sector.derivatives):=coalesce P farSet X (pp u) base a
  let upper (a:Mode F.sector.derivatives):=coalesce P (tree).leaves X p base a
  apply Weak.benefit (bands F.sector.derivatives h)
    (bands F.sector.derivatives 0) (demand F v X (tree).leaves p)
    (fun u=>demand F v X farSet (pp u)) c upper pay q eqpos
    (pow_nonneg (zero_le_one.trans L1) K) (pow_nonneg (div_nonneg hr.le ht.le) _) ht.le
  · have whole:=hf r x z o hr rt hx hz fz sep room sep2 v
    rw [VAC.difference F simple] at whole
    exact whole.trans (by rw [mul_comm t];exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ L1 kK) ht.le)
  · intro a ha'
    let e:A:=⟨a,ha'⟩
    have hK:ah e≤K:=by
      have paid:ah e≤∑u,ah u:=single_le_sum (fun u _=>Nat.zero_le (ah u)) (mem_univ e)
      dsimp [K];omega
    exact (ha e r x z o hr rt hx hz fz sep room sep2).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ L1 hK) (pow_nonneg (div_nonneg hr.le ht.le) _))
  · intro u hu
    let e:B:=⟨u,hu⟩
    have ihK:ih e≤K:=by
      have paid:ih e≤∑u,ih u:=single_le_sum (fun u _=>Nat.zero_le (ih u)) (mem_univ e)
      dsimp [K];omega
    have ohK:oh e≤K:=by
      have paid:oh e≤∑u,oh u:=single_le_sum (fun u _=>Nat.zero_le (oh u)) (mem_univ e)
      dsimp [K];omega
    have now:=nearRates e t x z o hx sep
    have next:=ho e r x z o hz (fun i=>by linarith [fz i]) sep2 v
    rw [VAC.difference F simple] at next
    have row:=Weak.product hr rt (norm_nonneg _)
      (pow_nonneg (zero_le_one.trans r1) _) (pow_nonneg (zero_le_one.trans t1) _) now next
    apply row.trans
    apply mul_le_mul_of_nonneg_right _ ht.le
    rw [mul_pow,mul_comm]
    exact mul_le_mul (pow_le_pow_right₀ t1 ohK) (pow_le_pow_right₀ r1 ihK)
      (pow_nonneg (zero_le_one.trans r1) _) (pow_nonneg (zero_le_one.trans t1) _)

end YM.OPE.Logged.Full
