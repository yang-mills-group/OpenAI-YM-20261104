import YM.PertExtension.BridgeClosure

/-!
# Image removal in every positive direction order

Both an abstract spacing statement used before sampling (joint scales with
origin placement), and its regulator consequences below, concern only Gaussian
pairings, not equality of higher coupling coefficients of actual states. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Next.Rank.Beamer Air Orb Orbit GaussianScore Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
open Projection
variable {G : Gauge} {q : ℕ+} {x : ℕ→Cover}{d : ℕ}
abbrev Port := PlaqAxes × G.ColorIndex
local notation "reg" => (Filter.atTop : Filter ℕ)
variable (hq:1<q.val)
include hq

lemma far_ref_point {X Y : ℕ→ Cover} (a b:Port (G:=G)) (d:ℕ) {r : ℝ}(hr:0<r) (hS:∀ᶠ k in reg,Screen r (side q k) (reflectedOffset (X k) (Y k) 0 a.1 0)):
 Filter.Tendsto (fun k=> magnify q k ^ d * (reflected G (side q k) (X k) (Y k) (0,a) (0,b) )) reg (nhds 0):=by
 obtain ⟨C,hC,h⟩:= image_point hr G
 refine squeeze_zero_norm' (a:= fun t=>C*(magnify q t^d/(side q t).val)) ?_ (by convert! (side_rate hq d).const_mul C using 2; exact (mul_zero _).symm)
 filter_upwards [hS] with k hk
 have hp : 0≤magnify q k^d:=pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _
 rw [norm_mul, Real.norm_of_nonneg hp]
 exact (mul_le_mul_of_nonneg_left (h _ _ _ _ _ a b hk) hp).trans_eq (by ring)
lemma far_ref_item {X Y : ℕ→ Cover} (a b:Address G) (d:ℕ) {r : ℝ}(hr:0<r) (hS:∀ᶠ k in reg,Screen r (side q k) (reflectedOffset (X k) (Y k) a.1 a.2.1 b.1)):
 Filter.Tendsto (fun k=> magnify q k ^ d * (reflected G (side q k) (X k) (Y k) a b)) reg (nhds 0):=by
   have ht:∀ᶠ k in reg, Screen r (side q k) (reflectedOffset ((X k)+a.1) ((Y k)+b.1) 0 a.2.1 0):=by simpa [reflectedOffset] using hS
   refine (far_ref_point (X:=fun k=>X k+a.1) (Y:=fun k=>Y k+b.1) hq a.2 b.2 d hr ht).congr (fun k=> ?_)
   unfold reflected stem; dsimp only; simp
lemma far_ref {X Y : ℕ→ Cover} (a b:Degree G){r:ℝ}(hr:0<r) (h:∀ i u v,∀ᶠ k in reg,Screen r (side q k) (reflectedOffset (X k) (Y k) u i v)) :
 Filter.Tendsto (fun k=> amount (magnify q k) a * amount (magnify q k) b * mourn (gesture a) (gesture b) (reflected G (side q k) (X k) (Y k))) reg (𝓝 0) :=by
  obtain ⟨s,hS⟩:=bright_gesture a; obtain ⟨t,hT⟩:=bright_gesture b
  let T:=4+(a.degree+b.degree); let L(k):Bridge G:=reflected G (side q k) (X k) (Y k)
  have hz k: amount (magnify q k) a* amount (magnify q k) b=magnify q k^T := by simp_rw [amount, ← pow_add]; congr 1; unfold T; omega
  let Q k i j := s i*t j*(magnify q k^T*L k i j)
  let H k := ∑ i∈s.support,∑ j∈t.support,Q k i j
  have ht i: Tendsto (fun k=>∑ j∈t.support,Q k i j) reg (𝓝 0):= by
      convert! tendsto_finset_sum t.support (fun j _=> (far_ref_item hq i j T hr (h i.2.1 i.1 j.1)).const_mul (s i*t j)) using 2
      simp
  suffices h:Tendsto H reg (𝓝 0) by
     refine h.congr (fun k=> Eq.symm ?_)
     change amount (magnify q k) a*amount (magnify q k) b*gesture a (fun i=> gesture b (L k i))=_; rw [hz]
     simp_rw [hS,hT,Finsupp.linearCombination_apply,Finsupp.sum,mul_sum,smul_eq_mul]
     simp only [mul_sum]
     exact sum_congr rfl fun i _=>sum_congr rfl fun j _=> show _* _=Q k i j by unfold Q;ring
  exact (tendsto_finset_sum s.support (fun i _=>ht i)).mono_right (le_of_eq (congr_arg nhds Finset.sum_const_zero))
lemma price_total {X Y : ℕ→Cover}{z₀:E4}(hz:z₀∈away)(h:Tendsto (fun k=> epsilon q k • mapZ (X k-Y k)) reg (𝓝 z₀))(a b:Degree G){r:ℝ}(hr:0<r)(hp:∀ i u v,∀ᶠ k in reg,Screen r (side q k) (reflectedOffset (X k) (Y k) u i v)) :
 Filter.Tendsto (fun k=> amount (magnify q k) a * amount (magnify q k) b * mourn (gesture a) (gesture b) (echo (side q k) (X k) (Y k))) reg (𝓝 (Prayer.gleam a b z₀)):=by
   have H:= (far_direct hq hz h a b).add (far_ref hq a b hr hp)
   simp only [PricePath, add_zero] at H
   convert! H using 1; funext k; rw [echo,map_add,mul_add]
end YM.PertExtension.LatticePT
