import YM.Juniper.LocalAtlas.Quotient
/-!
 # One real density computation price report – clean log of full Gaussian

 Graph connected by definition `blockTaylor n (log ∘ through n oneEra)`
 not entrywise exponential tagged. Needs no continuity of the real function
 relative its θ data outside healthy disk. Keeps arity independent dimension
 and prices prototype for AFTER block. `Wager` just finite list numeric, on
 local P generation below. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open MeasureTheory Set Function Matrix Metric Filter ProbabilityTheory
open PhysicalNext.Repeat Lantern RG Wilson
open ConnectedActivityE6 Blaze Brush Poll Sienna
open Work.G05 WilsonStartup Analysis Tensor
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {ι : Type}[Fintype ι][DecidableEq ι]
    {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {φ ψ : E × Poll.Body ι→ℝ}{ρ:E→ Poll.Body ι}{M : E→ Matrix ι ι ℝ}
    {k : ℕ}{D b p W q c: ℝ}
local notation "g" => grace φ ψ ρ M
local notation "K!"=> (M 0)⁻¹
local notation "μ" => sweep (M 0)⁻¹

section terms
variable {E' F : Type*}[NormedAddCommGroup E'][NormedSpace ℝ E'][NormedAddCommGroup F][NormedSpace ℝ F]
lemma home (n:ℕ)(P:PacketSeries E' F) : through n P 0= Tensor.diagonal (P 0) 0 := by
    unfold through; rw [Finset.sum_apply]; rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]; intro j h hj; simpa [hj] using Tensor.homogeneous (P j) 0 0
variable (φ ψ : E × Poll.Body ι→ℝ)(ρ:E→ Poll.Body ι)(M : E→ Matrix ι ι ℝ)
omit [FiniteDimensional ℝ E]
lemma quiet: coin φ ψ ρ M 0 = fun _z: Poll.Body ι=> Tensor.coeff (fun _ : ℝ×E=>(1:ℝ)) 0 0 := by
    ext z y; unfold coin Tensor.coeff
    simp [show ((0:ℝ), (0:E)) = (0 : ℝ×E) from rfl, Lantern.visit, Lantern.grace, iteratedFDeriv_zero_apply]
lemma ready (n:ℕ): through n (oneEra φ ψ ρ M) 0=1:= by
   rw [home,oneEra, quiet φ ψ ρ M]; simp only [integral_const,probReal_univ,one_smul]; exact Tensor.coeff_apply_zero ..
def cleanLetter (n : ℕ) := blockTaylor n (Real.log ∘ through n (oneEra φ ψ ρ M))
lemma blank (n:ℕ): cleanLetter φ ψ ρ M n 0=0:=by simp only [cleanLetter, blockTaylor_zero,Function.comp_apply,ready,Real.log_one]
end terms

variable {X W D₀ A a ε:ℝ} {n:ℕ} (hk:n+1 ≤ k)

-- use unit norm ∥y∥<b (eaves horizon) for both variables, normalize ∂^
-- comparisons by b (may shrink later).
local notation "λ#"=> Real.exp (-1)* (1/2:ℝ)
local notation "λ₀"=> λ# /2
local notation "u"=> Real.exp 1
local notation "ex"=> Icc λ₀ (u+ λ₀)
lemma fee_sign : (0:ℝ)< λ₀:= by positivity
structure Wager (D b W X A p a ε c : ℝ) (n k:ℕ): Prop where
    born : 1 ≤ D
    reserve : fee k p D*b≤1
    hp y : y ∈ Icc (-1:ℝ) 1 → Brush k W 1 Real.exp y
    log : Treasury k X λ₀ (u+ λ₀)
    fraction : 0<ε
    eve : a ≤ 1/2
    lift : let P:= preAux k p D W; let v:= clump k (fee k p D) W; let s:=overhead n k
           let Q:= P*(ε*gamut A c (2*((k+2)*k))+a*ε⁻¹)
           (v+s*v)*b^(n+1)+s*Q ≤ λ₀

def baseW (D W p:ℝ)(k:ℕ) := clump k (fee k p D) W
def XTag (D W p A c:ℝ)(n k:ℕ):= overhead n k*(preAux k p D W*gamut A c ((k+2)*k))
def debt₀ (D W p A c ε a:ℝ)(k:ℕ):= preAux k p D W*(ε*gamut A c (2*((k+2)*k))+a*ε⁻¹)
def net (D W p A c ε a b:ℝ)(n k:ℕ) := (baseW D W p k+overhead n k*baseW D W p k)*b^(n+1)+overhead n k*debt₀ D W p A c ε a k

def value (D W p X A c ε a b:ℝ)(n k:ℕ) := peg k (net D W p A c ε a b n k) (baseW D W p k) (XTag D W p A c n k) X +
        (clump k (XTag D W p A c n k) X + overhead n k* clump k (XTag D W p A c n k) X)*b^(n+1)

variable (H : Golf φ ψ ρ M k D b b p)
    (hc : ∀ z:ι→ℝ, dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ c * dotProduct z z)
    (T : Wager D b W X A p a ε c n k)(hT : (sweep (M 0)⁻¹).real (closedBall (0:Poll.Body ι) D)ᶜ ≤ a)(hA:(Fintype.card ι:ℝ)≤ A) {x:ℝ × E}
include T hk H hT hA hc
local notation "f!"=> ratify φ ψ ρ M D
local notation "P!" => through n (oneEra φ ψ ρ M)
local notation "O" => clump k (XTag D W p A c n k) X
local notation "s"=> overhead n k
local notation "p₀"=> baseW D W p k
local notation "t₀"=> net D W p A c ε a b n k
local notation "W₀"=> debt₀ D W p A c ε a k
local notation "W!"=> XTag D W p A c n k
lemma rising (hx:‖x‖<b): Brush k t₀ b⁻¹ (f! - P!) x ∧ (f! x ∈ ex ∧ P! x ∈ ex ∧ Brush k O 1 (Real.log ∘ P!) x) := by
  let Y:= ball (0:ℝ×E) b
  have hp:0 ≤ W:= (T.hp 0 (by simp)).nonneg
  have ht: fee k p D* max b b ≤1 := by rw [max_self]; exact T.reserve
  have he (x:ℝ×E)(hx:x∈Y): (Brush k p₀ 1 f! x ∧ Integrable (ballots φ ψ ρ M D x) μ)∧‖x.1‖<b ∧ ‖x.2‖<b:= by
     obtain ⟨h1,h2⟩:= (max_lt_iff).mp (mem_ball_zero_iff.mp hx : max ‖x.1‖ ‖x.2‖ < b); exact ⟨ Lantern.burs D H h2 h1 (by omega) ht T.hp hp,h1,h2⟩
  have hxY: x∈ Y := mem_ball_zero_iff.mpr hx
  have hV : b ≤ 1:= H.small
  have hu:1 ≤ b⁻¹:= (one_le_inv₀ H.pos).mpr hV
  obtain ⟨⟨hF,hI⟩,hu₁,hu₂⟩:= he x hxY
  have hm : 1/2 ≤ (μ).real (closedBall (0:Poll.Body ι) D) := by
    rw [measureReal_compl («μ»:=(sweep _)) measurableSet_closedBall, probReal_univ] at hT; linarith only [T.eve,hT]
  have ⟨hc',hv⟩:= Lantern.temperature D H hu₂ hu₁ (by omega) ht hI hm
  have hh (x:ℝ×E) (hx:‖x‖<b) : Brush k W! 1 P! x:= gross _ (fun i hi=> (coin_limit H T.born hc T.hp i (hi.trans (by omega)) hA).2) (hx.le.trans hV) k
  have hTX:= (hh x hx)
  let h:= f!; let P:= P!; let V:= blockTaylor n h
  have hW : Brush k t₀ b⁻¹ (h-P) x := by
    have he₀:= overall (fun x (hx:x∈Y)=> (he x hx).1.1) hV hk hx
    let w := s* W₀
    have hΔ : cap ( (fun i:ℕ=> Tensor.coeff h i 0) - oneEra φ ψ ρ M) n W₀ := fun i hi=> by
       let hc': i ≤ k:= hi.trans (by omega)
       dsimp only [Pi.sub_apply,h]; rw [norm_sub_rev, cuttable H T.born T.hp T.reserve (by omega) i hc']; exact debt H T.born hc T.hp i hc' hA T.fraction hT
    rw [show h-P=(fun x=> h x-V x+(through n ((fun i=> Tensor.coeff h i 0)-oneEra φ ψ ρ M) x)) from (by rw [through_diff]; funext y; dsimp only [Pi.sub_apply];rw [show through n (fun i=> Tensor.coeff h i 0) = V from rfl]; unfold P; abel)]
    exact he₀.gathering ((gross _ hΔ (hx.le.trans hV) k).climb le_rfl hu)
  have hp:= T.lift
  have hz: t₀ ≤ λ₀:= hp; have h₀': (0:ℝ)< λ₀:= fee_sign; have hw : ‖h x-P x‖ ≤ λ₀:= hW.bound.trans hz
  have hF': f! x∈ ex := ⟨by linarith only [h₀', hc'], hv.trans (le_add_of_nonneg_right h₀'.le)⟩
  have hP : P x ∈ ex :=by rw [Real.norm_eq_abs] at hw; unfold h P at hw; unfold P; constructor <;> linarith only [abs_le.mp hw,hv,hc']
  exact ⟨hW,hF',hP, Lantern.composite (hh x hx) (T.log.log (P x) hP)⟩
lemma fit (hx:‖x‖<b): Brush k (value D W p X A c ε a b n k) b⁻¹ (cleanLog φ ψ ρ M D - cleanLetter φ ψ ρ M n) x := by
  let h:= cleanLetter φ ψ ρ M n
  let y:= P!
  obtain ⟨hr,hf,hy,hY⟩ := rising hk H hc T hT hA hx
  have hv:= Lantern.burs D H ((norm_snd_le x).trans_lt hx) ((norm_fst_le x).trans_lt hx) (by omega) (by rw [max_self]; exact T.reserve) T.hp (T.hp 0 (by simp)).nonneg
  refine ((log_variation T.log fee_sign hv.1 (r:=P!) ?_ hf hy ((one_le_inv₀ H.pos).2 H.small) hr).gathering (overall (fun x hx => (rising hk H hc T hT hA (mem_ball_zero_iff.mp hx)).2.2.2) H.small hk hx)).shimmy ?_
  · exact gross _ (fun i hi=> (coin_limit H T.born hc T.hp i (hi.trans (by omega)) hA).2) (hx.le.trans H.small) k
  exact Eventually.of_forall fun z=> by change Real.log (f! z)-h z=Real.log (f! z)-Real.log (y z)+(Real.log (y z)-h z); ring
end YM.Juniper.LocalAtlas
