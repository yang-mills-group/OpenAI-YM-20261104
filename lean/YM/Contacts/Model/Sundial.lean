import YM.Contacts.Model.Province
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
namespace Province
open Slope Arbor Lintel.Plata ConnectedActivityE6 Next.Fluctuations Blaze Sienna
open Boulevard (actual)
variable {A H Z t b σ C Λ I μ d:ℝ}{S:ℝ≥0}{v:ℕ}{B:BudgetPoint}{X:G.ColorIndex}{P:Bed}{L:Side}
def width (z:ℕ):=2*z
lemma tile_cap (hz:20≤z)(i:Stars): (tiles z i).val≤Province.width z:= by rw [wings]; unfold width; have hx:= i.isLt; have hy:= foot_v hz; omega
-- simplify tail per unit price independent m!
def brinks (G:Gauge)(D : Stars→Side)(p:Clip)(Z μ C Λ A S:ℝ)(w k j:ℕ):ℝ:= (k:ℝ)*((Fintype.card (Loc G 1):ℝ) *(Real.exp (-S*w)*A)) +Model.pole μ (w+1)*sumFee G p (outerCost G j Z) μ C Λ j+∑ i:Stars, ‖Slide.ray i‖*inkjet G p Z μ C Λ A S w k j (D i)
lemma even_cost (D : Stars→Side)(p:Clip) : upPrice G D p Z μ C Λ A S w k j m= (Fintype.card (Site m):ℝ) * brinks G D p Z μ C Λ A S w k j := by
    let e:= inkjet G p Z μ C Λ A S w k j; unfold brinks upPrice; nth_rw 1 [inkjet]; rw [show Fintype.card (Lines G m 1)=Fintype.card (Site m) * Fintype.card (Loc G 1) from Fintype.card_prod ..]; push_cast; ring
variable (T:PathData G)(F:bore G)(p:Clip) (h:Aegis X F P)(hT:T.Bounds p μ I Λ)(hG:G.Simple)
variable (hx:∀ m,Dial P p T m)(ha:∀ m,Orbit T (hair F m) p)
variable (hk:2≤k)(hz:20≤z)(hi:i≤k)(hw:Tills (k+3) S C F)
variable (hB: Patron G B t σ z)(hW:10*z< m.val)(hZ:PaintSupply G B.order Z)(hy:sufficient G (Province.width z) (holdOn B.order (outerCost G B.order Z)) t)
def unitSize (G:Gauge)(t:ℝ)(B:BudgetPoint) (p:Clip)(z k:ℕ)(C Z μ I Λ:ℝ)(i:ℕ):ℝ := year B z (tollP G p (Province.width z) (k+3) B.order C (holdOn B.order (outerCost G B.order Z)) μ I Λ * t^(hero i))
def gapeSize (G:Gauge)(B:BudgetPoint):= (2:ℝ)⁻¹* (Fintype.card PlaqAxes:ℝ)*(pairBill G B*B.threshold^2)
lemma lays (G:Gauge)(B:BudgetPoint):0≤gapeSize G B:= mul_nonneg (by positivity) (mul_nonneg (pair_nonneg ..) (sq_nonneg _))
def aperture (z:ℕ):=z/4-1
lemma wide (hz:20≤z): 3≤ aperture z ∧ 2*(aperture z+1) ≤ foot z:= by unfold aperture foot; omega
lemma broad (hv:20≤z)(hu:10*z< m.val):4*(aperture z+1)+16 ≤ m.val:= by unfold aperture; omega
include h hT hG hx ha hk hz hi hw hB hW hZ hy
lemma offering (u:Site m): B.supBounds u (neighbors z u) (pass (bough k z T F p i) m u) (unitSize G t B p z k C Z μ I Λ i):= offered F p T h hT (wings z) hG (fun _=> hx _) (fun _=> ha _) hw (tile_cap hz) hi hk hB (by omega) (foot_v hz) u Z hZ hy
lemma nearby (δ:ℝ)(hb:‖proceeds k z T F p i‖≤δ)(u:Site m): B.supBounds u (neighbors z u) (pass (slice k z T F p i) m u) (unitSize G t B p z k C Z μ I Λ i + δ*gapeSize G B):= by
    exact sup_le (sup_sub (arb_bill T F p h hT hz hi B u) (face_bill _ _ (by omega)) (offering T F p h hT hG hx ha hk hz hi hw hB hW hZ hy u) (face_price _ _ G (by omega))) (add_le_add_right (mul_le_mul_of_nonneg_right hb (lays G B)) _)
def chief (G:Gauge)(D:Stars→Side)(p:Clip)(B:BudgetPoint)(m:Side)(z j:ℕ)(b Z μ C Λ A S:ℝ)(w k:ℕ):= (Slope.finale B m z j G D p b Z μ C Λ A S w k)
lemma wages (he:m.val=2*j)(hr: 3 ≤ i)(hW':PaintSupply G 2 A)(hs:0<S): ‖proceeds k z T F p i‖≤ chief G (tiles z) p B m z j (unitSize G t B p z k C Z μ I Λ i) A μ I Λ C S (aperture z) k:= by
   rw [identities T F p h hT hG hz hi B m (by omega)]; exact wind_price he (by omega) hW hG F h p T hT _ (arb_bill T F p h hT hz hi B) (offering T F p h hT hG hx ha hk hz hi hw hB hW hZ hy) hr hi hW' hs hw (broad hz hW) (wide hz).2 (wide hz).1
omit hZ hy hB hW hk hx ha
-- include precision
-- compute cost separable
lemma mission_upfront {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{U:E → Config G m}{y:E} (hQ:Inputs U j Z) (hh:d<1)(he:sufficient G (Province.width z) Z d)(hv:‖y‖≤d)(hu:1≤j)(x:Site m): Allows j (pass (slice k z T F p i) m x ∘ U) y (upCard G p (Province.width z) (k+3) j C Z μ I Λ + ‖proceeds k z T F p i‖*returnCost G Z 1 j):= by
   let b:=proceeds k z T F p i; have hb: flange G b=b • flange G 1:= by rw [← flange_power,mul_one]
   unfold slice; rw [hb]; exact votes' (upfront hQ T F h hG hw (by omega : i<k+3) _ (tile_cap hz) hT _ hh he hv hu _) ((cloverly 1 (fun i=>hQ.2.2 i y (hv.trans hh.le)) x).smul b)
include hW
lemma resilience (B:BudgetPoint)(hX:PaintSupply G j Z)(x:Link G m)(hh:j+i<k+3) : ‖jet (base p T m i ∘ input G m + plays (pass (slice k z T F p i) m)) j x - grate (hair F m) i j x‖ ≤ (Fintype.card (Site m):ℝ)*(brinks G (tiles z) p Z μ I Λ C S (aperture z) (k+3) j+‖proceeds k z T F p i‖*returnCost G (outerCost G j Z) 1 j)*‖x‖^j:= by
   let Y:= base p T m i ∘ input G m; let V:= plays (pass (slice k z T F p i) m); let A:= returnCost G (outerCost G j Z) 1 j; let t:=proceeds k z T F p i; let K:=plays (pass (flange G t) m); let K':= plays (pass (bough k z T F p i) m); have htF y := ((cloverly 1 (fun i=> imprints hX (show ‖(0:Link G m)‖≤1 by simp) i) y).smul t); change ‖jet (Y+V) j x- _‖≤_
   have hy: flange G t=t • flange G 1:= by rw [← flange_power,mul_one];
   have hf:Allows j K 0 ((Fintype.card (Site m):ℝ)*(‖t‖*A)):= by unfold K; apply Model.train; intro i; rw [hy]; exact htF i
   let M:= anchor p T F m (k+3) i ∘ input G m; let u:=moon F m (k+3) i; have hC : AnalyticAt ℝ Y 0:= armor_apt p T hT _; have hX' : AnalyticAt ℝ u 0:=(glowstar (should h.blazing) m k i (by omega)).analytic
   have hh': jet u j x=grate (hair F m) i j x:=by rw [certifiedStar (i:=j) (should h.blazing) m k i hh x,Nat.add_comm j i]; rfl
   have hh x: jet M j x= jet u j x - jet Y j x:=Ion.jet_minus u Y _ x hX' hC
   have hg: ‖jet K j x‖≤ (Fintype.card (Site m):ℝ)*(‖t‖*A)*‖x‖^j:= by
      let f':Link G m→ℝ:=0; have hy : (fun x:Link G m=> (0:ℝ))=0:=rfl; have htq:= jet_suff (f:=K) (g:=f') hf.analytic.analyticAt analyticAt_const (show Allows _ _ _ _ from ((sub_zero K).symm ▸ hf)) x; have hn: jet f' j x=0:= Convoy.jet_empty ..; rwa [hn,sub_zero] at htq
   have hb:=transforms p T F hT hw h hG (wings z) hX B (broad hz hW) (wide hz).1 (wide hz).2 x (show j+i<k+3 from by assumption); rw [even_cost] at hb; change ‖jet K' j x-jet M j x‖≤_ at hb;
   rw [serif hC V (froth_apt (germSlice T F p h hT hi)), ←hh', show V=K'-K from playMinus .., Ion.jet_minus K' K j x (froth_apt (energy_apt F h p T hT _ (by omega))) hf.analytic.analyticAt, mul_add (_:ℝ) (brinks ..), add_mul]; apply le_trans (le_of_eq (congr_arg norm (?_:_ =jet K' j x-jet M j x-jet K j x))) ((norm_sub_le ..).trans (add_le_add hb ?_)); · rw [hh]; ring
   exact hg
end Province
end YM.Contacts.Model
