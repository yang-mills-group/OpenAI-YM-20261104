import YM.RG12.Rail.Away
/-! Public `MeridianArc` now on Anemos RAY. Strengthen West/Dol (reusing proof structure
for prices after scaledX). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Set Filter Lattice Wilson RG Next.Rank Next.Rank.Atlas Station Next.Rank.Value
open Glimmer Prayer Configuration Perch Marker Glyph Cells Market Read Dock Camp Beamer Normal
open Wall Maxwell CellsInt
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G}{A:Levels G}{n d:ℕ}(h:G.Simple)(b e:ℝ)(he:0 < e)(hB:6 ≤ b)
variable {a:Points n} (ha:a∈conf n)
set_option quotPrecheck false
local notation "Y" k:max=> (A).clock.monitor k
private def rooted (a : Degree G) (p : Cover) : Degree G := { a with point:=p }
include h he hB ha
private lemma scaledR (i j : Fin n)(h₁:i≠j) (L S : Degree G) :
    ∀ᶠ k in atTop, ∀ x:Points n, Anemos a (Y k) (tested A b k x)→ ∀ p d H, Model A d k p H → ∀ X W,
      let f:= choose A b k x; let l := rooted L X; let s := rooted S W
      let K:= looked (H.κ k) (f i) (f j)
      let r:= mag A b k; let M:= moved x A b i j k X W
      attends d (wood A k) l → attends d (wood A k) s → (r⁻¹ • M) ∈ Maxwell.away ∧
        ‖amount r l*amount r s*mourn (gesture l) (gesture s) K - gleam L S (r⁻¹ • M)‖ ≤ bill (-4) (clim A k) ∧
          ‖amount r l * amount r s*mourn (gesture l) (gesture s) K‖ ≤ bill e (clim A k) := by
  have hb: 0 < b:=by linarith
  obtain ⟨C,c,hc,hC,hH⟩:= range_R (A:=A) h ha hb i j h₁ L S
  filter_upwards [hH,summery (A:=A) h (L.degree+S.degree) hB hc hC, (hat_rate A h).eventually ((bill_lo he).eventually_ge_atTop (C+1)), ((mag_rate A h hb).const_mul_atTop hc).eventually_ge_atTop 1] with k ht hM hl hV x hv p d H hp X Z
  intro f l s K r M ha hh
  have hz (L : Degree G) (hz : attends d (wood A k) L) : L.degree ≤ d-1 ∧ street L.point ≤ wood A k := by
    rcases hz with ⟨he,ht⟩|⟨he,ht⟩
    · exact ⟨by omega,by rw [he,empty_road]; exact Nat.zero_le _⟩
    exact ⟨he.le,ht⟩
  obtain ⟨he,hx,Ht⟩ := ht x hv X Z (hz _ ha).2 (hz _ hh).2
  have hs : 0<r := mag_pos ..
  let g := r⁻¹ • M; have ht : 1≤‖M‖ := le_trans hV he
  have hq : g∈away := smul_ne_zero (inv_pos.mpr hs).ne' (norm_pos_iff.mp (zero_lt_one.trans_le ht))
  have hv := hp.2 (f i) (f j) l s (hz _ ha).1 (hz _ hh).1 ht
  have hw : amount r l * amount r s= r^(4+(L.degree+S.degree)) := by
    dsimp only [amount, l,s,rooted]; rw [← pow_add];congr 1;omega
  let v := amount r l * amount r s
  have ha : ‖v * mourn (gesture l) (gesture s) K-gleam L S g‖ ≤ bill (-4) (clim A k) := by
    have hh : v*gleam l s M=gleam L S g := Eq.trans (b:=v*gleam l s (r • g)) (by unfold g; rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]) (grown l s hs g hq)
    rw [← hh,← mul_sub,norm_mul, Real.norm_of_nonneg (show 0≤ v by unfold v; rw [hw]; positivity)]
    apply (mul_le_mul_of_nonneg_left hv (show 0≤v by unfold v; rw [hw]; positivity)).trans; dsimp only [v]
    rw [hw,←mul_assoc]; exact hM p M he hx
  refine ⟨hq,ha, le_trans (show ‖v * _‖ ≤ ‖v* mourn (gesture l) (gesture s) K-gleam L S g‖+ ‖gleam L S g‖ from ?_) ?_⟩
  · generalize v*mourn (gesture l) (gesture s) K=z; exact le_trans (le_of_eq (congr_arg norm (sub_add_cancel z _).symm)) (norm_add_le ..)
  have hz : bill (-4) (clim A k) ≤ 1 := by grw [billed _ (by norm_num : (-4:ℝ) ≤ 0)]; rw [bill_zero]
  apply (add_le_add (ha.trans hz) Ht).trans; rw [add_comm 1 C]; exact hl

lemma chamberR (d : ℕ) : ∀ᶠ k in atTop, ∀ x:Points n, Anemos a (Y k) (tested A b k x)→ ∀ p H, Model A d k p H → ∀ i j,i ≠ j → MeridianArc A (bill e (clim A k)) (bill (-4) (clim A k)) (mag A b k) (wood A k) d k p
       (choose A b k x i) (choose A b k x j) (tested A b k x i) (tested A b k x j) H := by
  have Hx : ∀ᶠ k in atTop, ∀ i j, ∀ u v : Hub G (d+2) 0, i≠j →∀ x:Points n, Anemos a (Y k) (tested A b k x)→
      ∀ p H, Model A d k p H → ∀ X W,
        let l:=rooted u.val X; let s:=rooted v.val W
        let f:= choose A b k x; let K := looked (H.κ k) (f i) (f j)
        let r:=mag A b k; let M:=moved x A b i j k X W
        attends d (wood A k) l→ attends d (wood A k) s→ r⁻¹ • M ∈ away ∧
          ‖amount r l*amount r s*mourn (gesture l) (gesture s) K - gleam l s (r⁻¹ • M)‖ ≤ bill (-4) (clim A k) ∧
            ‖amount r l * amount r s*mourn (gesture l) (gesture s) K‖ ≤ bill e (clim A k) := by
    refine eventually_all.mpr (fun (i : Fin n) => eventually_all.mpr fun j => eventually_all.mpr fun u => eventually_all.mpr fun v => ?_)
    by_cases he' : i=j
    · exact Eventually.of_forall fun k H => False.elim (H he')
    refine (scaledR (A:=A) h b e he hB ha i j he' u.val v.val).mono fun k hf hv x hx p H hp Z T=> hf x hx p d H hp Z T
  filter_upwards [Hx] with k hk x hq p H hp i j hij
  let f:= choose A b k x; let z:=tested A b k x; let r:= mag A b k
  have he (L) (h : attends d (wood A k) L) : (rooted (G:=G) L 0).degree+2 ≤ d+2 := by
    unfold rooted; rcases h with ⟨_,ht⟩|⟨he,hl⟩ <;> dsimp only <;> omega
  let U (L : Degree G) (h) : Hub G (d+2) 0 := ⟨{ L with point:=0},rfl,Nat.zero_le _,he L h⟩
  refine ⟨hp.1 _ _, fun L S hX hW => ?_, fun u v => ?_⟩
  · have hL := hk i j (U L hX) (U S hW) hij x hq p H hp L.point S.point hX hW |>.2.2
    change ‖amount r L*amount r S*mourn (gesture L) (gesture S) _‖ ≤ _ at hL
    rw [norm_mul,norm_mul, Real.norm_of_nonneg (show 0≤amount r L from (pow_pos (mag_pos A ..) _).le), Real.norm_of_nonneg (show 0 ≤ amount r S from (pow_pos (mag_pos A ..) _).le)] at hL
    exact hL
  have hu : attends d (wood A k) u.val := Or.inl ⟨u.property.1,u.property.2.2⟩
  have hv : attends d (wood A k) v.val := Or.inl ⟨v.property.1,v.property.2.2⟩
  have hw := hk i j (U u.val hu) (U v.val hv) hij x hq p H hp u.val.point v.val.point hu hv
  let M:= moved x A b i j k u.val.point v.val.point
  have hm : r⁻¹ • M = z i-z j := by unfold M; rw [Wall.settled, u.property.1,v.property.1, sub_self, smul_zero,add_zero]
  have ht : z i≠z j := sub_ne_zero.mp (show z i-z j ∈ away from hm ▸ hw.1)
  rw [← glisten u.val v.val (z i) (z j) ht,← hm]; exact hw.2.1
end YM.RG12.Rail
