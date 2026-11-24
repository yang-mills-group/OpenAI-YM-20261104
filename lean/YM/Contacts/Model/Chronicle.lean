import YM.Contacts.Model.Letter
/-! Recover small-f price on the aggregate jets, despite lack of budget on simultaneous values at different periods. Symbols before flags. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric Push.Uniform Kale
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c:Side}{k w r z ℓ i j:ℕ}
namespace Province.Costing
open Slope Arbor ConnectedActivityE6 Next.Fluctuations Blaze Sienna Lintel.Plata Barrage.Reserve
variable {A Z s t C Λ I μ a d r ε:ℝ}{S:ℝ≥0}{f g:ℝ→ℝ}{p:Stage}{B:BudgetPoint} (G)
structure Charted (k:ℕ)(x:ℝ)(B:BudgetPoint)(T:PathData G)(F:bore G)(p:Clip)(d v a:ℝ)(i:ℕ)(j:ℕ) : Prop where
    sector (m:Side) (z:Site m): B.Regular (neighbors B.B z) (pass (slice k B.B T F p i) m z)
    connected : Adapted (slice k B.B T F p i) ∧ LocalOn (Lattice.box B.B) (slice k B.B T F p i)
    projection (m:Side)(h:10*B.B< m.val)(y:Site m) : ∀ u v, IsAffineDirection y u→ IsAffineDirection y v→logHessian (pass (slice k B.B T F p i) m y) u v=0
    order (m:Side)(x y) (e:ℕ): e<hero i → jet (pass (slice k B.B T F p i) m x ∘ input G m) e y=0
    hull (m:Side)(u:Site m) : altitude (pass (slice k B.B T F p i) m u) ∧ pass (slice k B.B T F p i) m u 1=0
    funds (m:Side)(h:10*B.B< m.val)(y:Site m) : B.supBounds y (neighbors B.B y) (pass (slice k B.B T F p i) m y) (x^(vow*hero i + a))
    shine (m:Side)(y:Site m)(z:Link G m): ‖z‖≤ v → Allows j (pass (slice k B.B T F p i) m y ∘ input G m) z (x^a)
    precise (m:Side)(h:10*B.B< m.val)(y : Link G m)(l: ℕ): l+i<k+3 → ‖jet (base p T m i ∘ input G m + plays (pass (slice k B.B T F p i) m)) l y - grate (hair F m) i l y‖ ≤ (Fintype.card (Site m):ℝ)*x^(-d)*‖y‖^l
abbrev ripe (x:ℝ) := x^(-(2/5):ℝ)
variable {G}
variable (H:G.Simple)(hZ:0<ε)(hf:Flat G f)(ht:Flat G g)(hk:2≤k)(hi:i≤k)
variable (p k)
include H hf ht hk hi
private lemma tintPower (j:ℕ) (d:ℝ) : ∀ᶠ x:ℝ in atTop,∀ F:bore G,∀ (T:PathData G)(B:BudgetPoint),Lodged B p x→ Witnessed G k x p B F T (f x) (g x)→∀ (m:Side),10*B.B< m.val→∀ y: Link G m, j+i<k+3 → ‖jet (base p.clip T m i ∘ input G m + plays (pass (slice k B.B T F p.clip i) m)) j y - grate (hair F m) i j y‖ ≤ (Fintype.card (Site m):ℝ)*x^(-d)*‖y‖^j := by
   obtain ⟨Z,hZ⟩:=paint_supply G j; obtain ⟨Y,hY⟩:=paint_supply G p.order
   let a:= -1-d; let w:= p.width; let s:= p.paths; let A:=returnCost G (outerCost G j Z) 1 j;
   let v(x:ℝ):=brinks G (tiles (radiusB x)) p.clip Z w s (g x) (f x) (narrow x) (aperture (radiusB x)) (k+3) j+x^a*|A|
   have he:Rate G 1 a v:= Rate.add (surrender p.clip p.width_pos hf ht) ((power _).mul_right _); filter_upwards [ample,lodge k p H hf ht hk hi a Y hY,faster he (by unfold a; linarith : a < -d)] with x ht hx hb F T B h h' m hc y hh; obtain ⟨z,O,hO,hM⟩:= h'.source; rw [h.box] at hc ⊢
   apply (resilience T F p.clip hO h'.nails H ht hi h'.fare hc B hZ y hh).trans; apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _); apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); apply le_trans _ ((le_abs_self (v x)).trans hb); apply add_le_add_right; -- may term order; bound abs path
   exact le_trans (mul_le_mul_of_nonneg_left (le_abs_self A) (norm_nonneg _)) (mul_le_mul_of_nonneg_right (hx F T B h h').1 (abs_nonneg _))
include hZ
lemma towerUp (j:ℕ) (d:ℝ): ∀ᶠ x:ℝ in atTop,∀ F:bore G,∀ (T:PathData G)(B:BudgetPoint),Lodged B p x→ Witnessed G k x p B F T (f x) (g x)→ Charted G k x B T F p.clip d (ripe x) ε i j := by
   have ho l (_h:l∈Finset.range (k+3)):= tintPower k p H hf ht hk hi l d; obtain ⟨Z,h₁⟩:=paint_supply G (j+1); obtain ⟨Y,hY⟩:=paint_supply G p.order; let d':= vow*hero i
   let A(x:ℝ):= shard p k i x G (f x) Y (g x) + x^d'*bank G (temp x) p.order p.power; let W:=outerCost G (j+1) Z; let P':=returnCost G W 1 (j+1)
   let π (x:ℝ):= upCard G p.clip (Province.width (radiusB x)) (k+3) (j+1) (f x) W p.width p.paths (g x)+x^d'*|P'|
   have ha: Rate G 1 d' A:= Rate.add (frequency k p hf ht) (joinPower (power _) (pleasantBank p G) (by simp))
   have he:Flat G π:= (summitArc p.clip hf ht).add (((power d').mul_right _).weaken (mul_nonpos_of_nonpos_of_nonneg vow_ok.le (Nat.cast_nonneg _)))
   filter_upwards [ample,(eventually_all_finset _).mpr ho,lodge k p H hf ht hk hi d' Y hY,confidence G W _ (show -(2/5:ℝ)<0 by norm_num), faster he hZ, faster ha (show d'< d'+ε by linarith), (tendsto_rpow_neg_atTop (show 0 < (2/5:ℝ) by norm_num)).eventually_lt_const zero_lt_one] with x hz hT hx hK hy hA hr F T B hh hD
   let z:=radiusB x; obtain ⟨χ,O,hO,H'⟩:= hD.source; obtain ⟨hk',hH⟩:= hx F T B hh hD
   refine ⟨fun m u=>hh.box ▸ atlas (z:=z) T F p.clip hO hD.nails hz hi B u, hh.box ▸ ⟨adapted_piece (G:=G) k z T F p.clip i,slice_local T F p.clip hz i⟩, fun m hw y=> hh.box ▸ wreck T F p.clip hO hD.nails H hz hi B y (hh.box ▸ hw),fun m u y e he=> hh.box ▸ lease_vanish T F p.clip hO hD.nails H H' hD.panel hk hz hi B m u y he, fun m u=> ?_,fun m hw u=> ?_,fun m u y hu=>?_,fun m hm y i hi=> hT i (mem_range.mpr (by omega)) F T B hh hD m hm y hi⟩
   · rw [hh.box]; exact ⟨germSlice T F p.clip hO hD.nails hi u,slice_unit T F p.clip hO hD.nails H H' hD.panel hk hi _⟩
   · rw [hh.box]; apply sup_le (sup_sub (arb_bill T F p.clip hO hD.nails hz hi B _) (face_bill (proceeds k (radiusB x) T F p.clip i) B (by omega)) (hH m hw u) (face_price _ _ G (by omega))); apply le_trans _ ((le_abs_self _).trans hA); apply add_le_add_right; let a:= bank G (temp x) p.order p.power; have hx:gapeSize G B=a:= (by unfold a bank gapeSize VerifiedReset.pairBill; rw [hh.order,hh.power,hh.threshold]); change _ ≤ x^d' * a; rw [← hx]; exact mul_le_mul_of_nonneg_right hk' (lays G B)  -- maybe rewrite
   · rw [hh.box]; let V:=pass (slice k z T F p.clip i) m u ∘ input G m; apply ((mission_upfront T F p.clip hO hD.nails H hz hi hD.fare (enoughChart h₁) (show ripe x<1 from hr) hK hu (by omega) u).order (Nat.le_succ j)).mono; apply le_trans _ ((le_abs_self (π x)).trans hy); exact add_le_add_right ((mul_le_mul_of_nonneg_left (le_abs_self P') (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right hk' (abs_nonneg _))) _
end Province.Costing
end YM.Contacts.Model
