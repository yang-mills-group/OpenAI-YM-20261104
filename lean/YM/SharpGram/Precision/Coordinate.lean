import YM.SharpGram.Precision.Grid
/-!
# Paying for frame-transform of a multi-mark numerical error

Works also with variable geometry, norms (may be zero), connected or ordinary
coefficients on the same measure, and derivative/spectator index. This is the
outward error transform e.g. fixed label tensor components. It doesn't
truncate an expansion of order R back to r while assuming its terms can be
estimated in these more expensive frames at unchanged coupling power. For
that application, separate coefficient hypotheses on the truncated tail are
needed; don't infer fixed-label Λ^q bounds from measuring coordinate Λ^q.
(See discard-lemma keeping inputs already in target numerical array norm *where
available*.) R depends on prices of the chosen fields/functionals, caller can
apply simultaneously to a basis. Don't infer λ versus spacetime lengths
from support remainders other than the theorem's explicit `B.proper`.

The TRUE measuring frames here from Mantle are not joined to a canonical
frame in another scheme, or to length `~ Λ^q a_k` (basis is at B.radius).
This example use of the estimate works wherever the comparison on the left
premise can be made independently, in any such geometry & allocation cut.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Allow
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open Org Spec Next.UVStress Annulus Lenses OPE MergeProof
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{u:Filter (ℕ×ℕ)}
variable {F:Final C f S}
variable (B : Mantle F u) (h : Annulus.Fits F)
local notation "P"=> C.path.levels.clock.hatBeta
local notation "a!"=> C.S.a
local notation "V"=>F.sector.derivatives
local notation "T"=> (Bel C.book)
variable (hG : G.Simple) {n d w:ℕ}
variable (p:Caps n)(x : Ribbon S p) (L:S.Field d →ₗ[ℂ] ℂ)
include B h hG
set_option maxHeartbeats 800000 in
lemma transforms (hw:w ≤ d)(hL:Kills (C:=C) V hw L)(r g₀:ℕ) :
    ∃ A:ℕ, ∀ (R s:ℕ), outputPower r (A+g₀) ≤ R →
     -- all retained periods, couplings, polynomial-log costs included
      ∀ᶠ k in atTop, ∀ β∈Band C k, ∀ η:ℝ, η≤1 → ∀ b:ℝ, 0≤b→
        ∀ E : MultilinearMap ℂ (fun i:Fin n=> S.Field (p i)) (S.Field d),
        (∀ t: Ribbon (Bel C.book) p,
          ‖(B.lens k d).symm (E (fun i=>B.lens k (p i) (t i)))‖ ≤
            P k ^ g₀ * coupling β ^ ((R:ℝ)+1-η) * Lambda C k ^ s * b * ∏ i, ‖t i‖) →
        ‖L (E x)‖ * (∏ i, a! k ^ p i) / a! k ^ w ≤
          2^(A+g₀) * coupling β ^ (r+1) * Lambda C k ^ s * b := by
   choose l hl using (fun i:Fin n=> inbound_price h B hG (x i))
   obtain ⟨o,ho⟩:=outbound_price h B hG L hw hL
   let X:= ∑ i,l i
   refine ⟨o+X,fun R s hr=>?_⟩
   filter_upwards [eventually_all.mpr hl,ho,later C hG] with k hk hv hK β hβ η he b hb A hA
   let v : Ribbon (Bel C.book) p:=fun i=> (B.lens k (p i)).symm (x i)
   have ht':0<P k:=zero_lt_one.trans (C.path.levels.fits.delayed _); have ha := C.S.a_pos k
   have ht := coupling_pos hβ; have hR : 0<coupling β ^ ((R:ℝ)+1-η):=Real.rpow_pos_of_pos ht _
   let W:ℝ:= ∏ i:Fin n, a! k ^ p i; have hW:0<W:=by unfold W; positivity
   let Z:= Lambda C k ^ s * b; have hZ:0≤Z:= mul_nonneg (pow_pos (lambda_pos ..) s|>.le) hb
   specialize hA v; rw [show ((fun i => B.lens k (p i) (v i)) : Ribbon S p)=x from funext (fun i=> LinearEquiv.apply_symm_apply ..)] at hA
   specialize hv ((B.lens k d).symm (A x)); rw [LinearEquiv.apply_symm_apply] at hv
   have hz : ∏ i, ‖v i‖ ≤ P k^X / W:=
      (Finset.prod_le_prod (fun i _=>norm_nonneg (v i)) (fun i _=> hk i)).trans_eq (by unfold W X; rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]) -- name
   have H: ‖L (A x)‖ ≤ P k^o * a! k^w * (P k^g₀ * coupling β ^ ((R:ℝ)+1-η) * Z * (P k^X/W)) := hv.trans (mul_le_mul_of_nonneg_left (hA.trans (by
        rw [show _ * _ * (Lambda _ _) ^ _ * b = P k^g₀ * coupling β ^ ((R:ℝ)+1-η) * Z from by unfold Z; ring] -- fill
        exact mul_le_mul_of_nonneg_left hz (by positivity))) (by positivity))
   apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right H hW.le) (pow_pos ha w|>.le)).trans
   calc
      _ = (P k ^ (o+X+g₀)*coupling β ^ ((R:ℝ)+1-η)) * Z:= by simp only [pow_add]; field_simp
      _ ≤ _ := (mul_le_mul_of_nonneg_right (internal hβ (hK _ hβ) hr he) hZ).trans_eq (by unfold Z; ring)

omit B h hG

-- Only when the FUTURE discarded predictions are bounded in THIS target
-- norm with Lambda-polynomial precision. Not automatically in fixed-field
-- conversion of series with nontrivial frame factors. Useful for RG05.
theorem discard {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {v : ℝ}{H b : ℝ} {r R k s:ℕ}
    (hr:r ≤ R)(hv:v∈Band C k)(ht:coupling v ≤ 1) (he:0≤H) (hb:0 ≤ b)
    (f : ℕ→E) (p:E)
    (hx : ∀ i:ℕ,r < i → i ≤ R→ ‖f i‖ ≤ H*(Lambda C k)^s*b)
    (hp : ‖p- ∑ i∈Finset.range (R+1), coupling v ^ i • f i‖ ≤ H * coupling v^(r+1) * (Lambda C k)^s * b) :
    ‖p- ∑ i∈ Finset.range (r+1), coupling v ^ i • f i‖ ≤ ((↑(R-r+1):ℝ)*H) * coupling v^(r+1) * (Lambda C k)^s * b:= by
   let M:=H * coupling v^(r+1) * (Lambda C k)^s * b; let w i:=coupling v ^ i • f i
   let S i:=∑ j∈Finset.range (i+1),w j
   have hv0 : 0≤M:= by have := lambda_pos C k; have := coupling_pos hv; positivity
   have hh : ∀ q, r ≤ q→ q ≤ R → ‖S q - S r‖ ≤ (↑(q-r):ℝ)*M := by
       intro i hi; induction i, hi using Nat.le_induction with
       | base=> simp
       | succ i hi ih =>
          intro hh; specialize ih (by omega); rw [show S (i+1) - S r = S i - S r + w (i+1) from by unfold S; rw [Finset.sum_range_succ _ (i+1)]; abel]
          have hv':0<coupling v:=coupling_pos hv
          have h: ‖w (i+1)‖ ≤ M :=by
            unfold w; rw [norm_smul,Real.norm_of_nonneg (pow_pos hv' _ |>.le)]
            refine (mul_le_mul (pow_le_pow_of_le_one hv'.le ht (Nat.add_le_add_right hi 1)) (hx _ (by omega) hh) (norm_nonneg (f (i+1))) (by positivity)).trans_eq ?_
            unfold M;ring
          exact (norm_add_le ..).trans ((add_le_add ih h).trans_eq (by push_cast [hi, Nat.sub_add_comm hi]; ring)) -- maybe
   change ‖p-S r‖ ≤ _
   rw [show p-S r=p-S R+(S R-S r) by abel]
   exact (norm_add_le ..).trans ((add_le_add hp (hh R hr le_rfl)).trans_eq (by unfold M;push_cast [hr]; ring))
end YM.SharpGram.Allow
