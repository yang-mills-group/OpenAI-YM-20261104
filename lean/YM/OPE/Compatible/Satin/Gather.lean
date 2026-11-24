import YM.OPE.Compatible.Satin.Studio
/-!
# Linearize any slot-wise readout across a subtree comparator with full *loaded* letters. Canonical width for charging chosen d, not minimal grade yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(P:Prescription T.sector.derivatives){u:X}
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "B"=> bands L
local notation "H"=> brim D (Arboreal.trim U u)
local notation "V"=>brim D U
local notation "Θ"=> glen D U u
-- full ink
-- rationale

def fullInk (d:ℕ)(b:Mode T.sector.derivatives): C.label d:= S.representative d (P.loaded b d)
def pallet (p:X→ C.book.Token)(z:C.book.Token)(u:X): X → C.book.Token:= update p u z
variable (x:X→E4)(p:X→ C.book.Token) (d n : ℕ) (h:P.Coherent)
include h
lemma throughMarked (g:S.Field d→ₗ[ℂ]ℂ)(a:C.label d): g (S.project _ a)=∑ b∈ bands L d,P.test b d (S.project d a)*g (S.project _ (fullInk T P d b)):=by
    conv_lhs => rw [← (h _).rebuilds (S.project _ a), map_sum]
    simp_rw [map_smul]; apply sum_congr rfl; intro b hb; unfold fullInk; rw [S.rep]; rfl
variable (a:C.label d){α α' β' t σ:ℝ} -- σ=W_child/T^d ; β'=Wt ; total weight t=σ β'
local notation "Y"=> picked Θ x
local notation "X!"=> picked H x
local notation "f"=>fun b:Mode L=>P.ope b (picked Θ x) (picked Θ p) (x u)
variable (u)
set_option quotPrecheck false
variable (F': Finset (Mode T.sector.derivatives)) -- fixture
-- counting product error. weighted left cost grant α' for ANY fullInk readout already accounted, positive β etc.
include h
lemma backGains (g : S.Field d→ₗ[ℂ]ℂ) (w: Mode T.sector.derivatives →ℝ)
    (hσ:0 ≤ σ)(hβ:0 ≤ β') (hα:0≤α)
    (hu : ∀ b∈ bands L d, ‖P.ope b (picked Θ x) (picked Θ p) (x u)-P.test b d (S.project _ a)‖ ≤ α)
    (hh:∀ b∈ bands L d,β' * ‖g (S.project _ (fullInk T P d b))‖ ≤ w b):
    σ*β'*‖g (S.project d a) - ∑ b∈bands L d,P.ope b (picked Θ x) (picked Θ p) (x u)*g (P.loaded b d)‖ ≤ (α*σ)*∑ b∈bands L d,w b:=by
    let c:= σ*β'; have h0:0 ≤ c:= mul_nonneg hσ hβ; rw [throughMarked T P d h g a,← Finset.sum_sub_distrib]; unfold fullInk at *; simp_rw [S.rep] at *
    apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) h0).trans
    rw [Finset.mul_sum,Finset.mul_sum]; refine Finset.sum_le_sum fun i hi=>?_ ; rw [← sub_mul,norm_mul,norm_sub_rev]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hu _ hi) (norm_nonneg _)) h0).trans ((show _ from le_of_eq (by change σ*β'*(α*‖g (P.loaded i d)‖)=α*σ*(β'* ‖g (P.loaded i d)‖); ring)).trans (mul_le_mul_of_nonneg_left (hh _ hi) (mul_nonneg hα hσ))) -- hole
-- use on functional on labels operation (readable work)
lemma compareLinear (F:C.label d→ℂ) (G:S.Field d→ₗ[ℂ]ℂ)(hG:∀ a,F a=G (S.project d a))(w:Mode T.sector.derivatives→ℝ) (hσ:0 ≤ σ)(hβ:0 ≤ β')(hα:0≤α)
    (hu : ∀ b∈ bands L d, ‖P.ope b (picked Θ x) (picked Θ p) (x u)-P.test b d (S.project _ a)‖ ≤ α)
    (hh:∀ b∈ bands L d,β' * ‖F (fullInk T P d b)‖ ≤ w b):
    σ*β'*‖F a- ∑ b∈bands L d, P.ope b (picked Θ x) (picked Θ p) (x u)*F (fullInk T P d b)‖≤ (α*σ)*∑ b∈bands L d,w b:=by
    simp_rw [hG] at hh ⊢; have ht:= backGains D T P u x p d h a G w hσ hβ hα hu hh; unfold fullInk; simp_rw [S.rep]; exact ht -- arg order u earlier
-- expensive second match readout vs P tested remainder of Delta_a
local notation "M" => picked V x
local notation "M'"=> picked V p
local notation "Q'"=> picked H (update p u (⟨d,a⟩:C.book.Token))
variable [Fintype I] (z:I→ E4) (q:I→ C.book.Token)(r:Viewers T) {y:C.label n}
local notation "K"=> spectator T r
local notation "v'"=> observe K
local notation "T!"=>P.truncated K n
lemma boundSecond (hy:Injective (beside (sole (0:E4)) z)) {b:ℝ}
    (hk: ‖observe (spectator T r) (beside M z) (beside M' q)- observe K (beside X! z) (beside Q' q)-observe K (beside (sole (0:E4)) z) (beside (sole (⟨n,y⟩:C.book.Token)) q)‖ ≤ b)
    (hP:∀ i∈ bands L n, ‖P.ope i M M' 0-P.ope i X! Q' 0-P.test i n (S.project n y)‖≤ b)(h0:0≤ b)(hE:∀ i∈bands L n, ‖observe K (beside (sole (0:E4)) z) (beside (sole (P.letter i)) q)‖ ≤ t):
    ‖(observe K (beside M z) (beside M' q)- T! M M' 0 z q)-(observe K (beside X! z) (beside Q' q)- T! X! Q' 0 z q)‖ ≤ b+ ↑(bands L n).card*(b*t):=by
    let d:=observe K (beside M z) (beside M' q)-observe K (beside X! z) (beside Q' q); let f':=observe K (beside (sole (0:E4)) z) (beside (sole (⟨n,y⟩:C.book.Token)) q); let p':= T! M M' 0 z q- T! X! Q' 0 z q
    have hA : ‖p'-f'‖ ≤ ↑(bands L n).card*(b*t):=by
        unfold p' f' Prescription.truncated Prescription.termRead; rw [← sum_sub_distrib, ← P.sumAll (spectator T r) q (spectate_ready T r) (spectate T r).laws.toSymmetric (spectate_respects T r) hy h,← sum_sub_distrib]
        refine (norm_sum_le ..).trans (le_trans (b:=∑ i∈bands L n,b*t) ?_ (le_of_eq (by simp))); refine Finset.sum_le_sum fun i hi=>?_; rw [← sub_mul, ← sub_mul, norm_mul]; exact mul_le_mul (hP _ hi) (hE i hi) (norm_nonneg _) h0
    let c:= (v') (beside M z) (beside M' q); let c':= T! M M' 0 z q; let e:=(v') (beside X! z) (beside Q' q); let e':= T! X! Q' 0 z q
    have hz : c-c'-(e-e')=(d-f')-(p'-f'):=by change _=(c-e-f')-(c'-e'-f'); abel
    change ‖c-c'-(e-e')‖≤_; rw [hz]; exact (norm_sub_le ..).trans (add_le_add hk hA)
end YM.OPE.Arboreal.Trace
