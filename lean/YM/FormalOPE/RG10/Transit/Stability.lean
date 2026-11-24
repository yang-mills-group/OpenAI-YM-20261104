import YM.FormalOPE.RG10.Transit.Flock

/-!
# Explicit remaining single-series transmission hypotheses

Separate actual spacing control from all graph assumptions. Only already *invariant* series
(algebra of germs retained by the caller) in the raw formal normalization may be passed. These
are consumer hypotheses, requiring any repeated-transfer estimate at a prescale parameter choice,
not automatically satisfied by any RG capacity estimates (not even real-side S3).

Esthetics `march` etc fine direction only where μ ≤ R. Could also apply throughout a slab with
`R` chosen as far scale and consequently costs including its log at the near scale. Rooted moments
required WITHOUT estimates on any multi-cluster packets; explicitly on
actual unrestricted-invariant-argument maps but with the kernel polynomial calculus `Episode`.
Thus while taking the UV-finer-tail history one can retain precisely the difference/norm hypothesis
supplied by RG08/09 needed at each operation or stop; we do not compose the estimates on all steps
as though counting a fixed number of steps. Window indices `k≤t≤N` or `k≤j<N` only. No cutoff
comparison in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Finset Function
open scoped Topology BigOperators Classical
variable {U J : ℕ→ Type} {X : Type}
variable (V : Voyage U J) (W : Scale X U) [∀ i,Fintype (J i)] [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)] (R C : ℝ) (δ : ℕ)
local notation "Y" => W.Y C R
local notation "μ" => W.μ
local notation "m" => W.eyes

structure Hours (W : Scale X U) (R C:ℝ) (δ b N:ℕ) : Prop where
  rich : 2 ≤ C
  base : W.μ b ≤ R
  neighbor : ∀ i∈ Ico b N,W.μ i ≤ W.Y C R i ^ δ * W.μ (i+1)
  year : ∀ i∈Ico b N,W.Y C R (i+1) ≤ W.Y C R i ^ δ

variable (F : ∀ i, Subring (Channel (U i)))
structure Regular (V : Voyage U J) (W : Scale X U) (R C : ℝ) (δ b N r d n : ℕ) (F : ∀ i, Subring (Channel (U i))) (O : Lens W.tape) : Prop extends Hours W R C δ b N where
  fund : ∀ i∈Ico b N, V.regular W r d n i (W.Y C R i ^ δ)
  selfish : V.authentic F b N
  stable : ∀ i∈ Icc b N,∀ j∈ Icc i N,∀ P∈F j, Guard P r d →
      W.value i n r O (V.yield i j P) ≤ W.Y C R j ^ δ * W.value j n r O P
-- using drop smaller windows no new estimates. On same regulator geometry
namespace Regular
variable {V W R C δ F} {b N k r d n t i : ℕ} {O : Lens W.tape}

lemma clip (h:Regular V W R C δ b N r d n F O) (hb:b ≤ k) (ht:t ≤ N) : Regular V W R C δ k t r d n F O := by
  have hi := Ico_subset_Ico hb ht
  exact ⟨⟨h.rich,(W.decrease hb).trans h.base,fun i h' => h.neighbor i (hi h'),fun i h' => h.year i (hi h')⟩,
     fun i h' => h.fund i (hi h'),h.selfish.clip hb ht,
     fun i h' j he=> h.stable i (Icc_subset_Icc hb ht h') j (Icc_subset_Icc le_rfl ht he)⟩
lemma rank (h:Regular V W R C δ b N r d n F O) : V.Eligible r b N := fun i hi=> (h.fund i hi).toEligible
lemma at2 (h:Regular V W R C δ b N r d n F O) (he : b ≤ i) : 2 ≤ W.Y C R i := W.rich R C h.base h.rich he
end Regular
end YM.FormalOPE.RG10.Transit
