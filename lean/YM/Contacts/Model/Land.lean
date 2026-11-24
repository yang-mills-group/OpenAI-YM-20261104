import YM.Contacts.Model.Enroll
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
variable {σ:ℝ≥0}{A C μ Λ Z :ℝ} (p:Clip)(R:PathData G)(F:bore G) {P:Bed}{X:G.ColorIndex}
    (h:R.Bounds p μ C Λ)(hw:Tills (k+3) σ A F)(he: Aegis X F P)(hg:G.Simple)
local notation "L" => Link G m
-- pass tilt differs all periods
lemma ice {V:Story G}(h:Adapted V) : hue V=V:= by
   funext x; unfold hue; simp_rw [show ∀ i:Signed,V (pull i 0 x)=V x from fun i=>h i x]; rw [sum_const, nsmul_eq_mul, card_univ, ←mul_assoc, factor_card,one_mul] -- V impl
lemma playMinus (F U:Story G): plays (pass (F-U) m)= (plays (pass F m)) - (plays (pass U m)):= by ext x; simp [plays,pass,froth,sum_sub_distrib]

def anchor (m:Side)(k i:ℕ): Config G m→ℝ := Kale.mirror (Kale.fire (wind (hair F m) k i))-base p R m i
-- bare model from Ledger and (all uncut) tile.
def cheek (w k i:ℕ): Story G:= lines w F k i- hue (boats p R (some (w+1)) i)
lemma stays (k i:ℕ)(hw:3≤w): LocalOn (Lattice.box (w+1)) (cheek p R F w k i) := fun _ _ hh=> congr_arg₂ (·-·) (lines_loc w F k i _ _ hh) (resides p R (by omega) i _ _ hh) -- hW metavars
lemma touches : Adapted (cheek p R F w k i):= fun s U=> congr_arg₂ (·-·) (lines_boat w F s U) (paints _ s U)
def inkjet (G:Gauge)(p:Clip)(Z μ C Λ A S:ℝ)(w k j:ℕ)(m:Side):ℝ := (k:ℝ)*((Fintype.card (Lines G m 1):ℝ)*(Real.exp (-S*(w:ℝ))*A))+ (Fintype.card (Site m):ℝ)*(Model.pole μ (w+1)*sumFee G p (outerCost G j Z) μ C Λ j)
include h
lemma anchor_d (a:Option ℕ)(i:ℕ)(x:Site m) : altitude (pass (hue (boats p R a i)) m x) := adapted_hue (sand_bar p R a h i) x
lemma armor_apt (i:ℕ) : altitude (base p R m i):= by rw [← uses]; exact froth_apt (anchor_d p R h _ _) -- change
lemma cheek_t (w k i:ℕ)(x:Site m): altitude (pass (cheek p R F w k i) m x):= (lines_l w F (k:=k) (i:=i) x).sub (anchor_d p R h _ _ x)
include he
lemma anchor_apt (hk:i<k+3): altitude (anchor (G:=G) p R F m (k+3) i):= (glowstar (should he.blazing) m k i hk).analytic.sub (armor_apt p R h i)
include hw hg
lemma abroad (hZ:PaintSupply G j Z)(x:L)(hi:j+i<k+3) (w:ℕ) : ‖jet (plays (pass (cheek p R F w (k+3) i) m)) j x - jet (anchor p R F m (k+3) i ∘ input G m) j x‖ ≤ inkjet G p Z μ C Λ A σ w (k+3) j m * ‖x‖^j:= by
   let v:= pass (lines w F (k+3) i) m; let a:= pass (hue (boats p R (some (w+1)) i)) m; let u:= wind (hair F m) (k+3) i; let T:= base p R m i ∘ input G m; let Y:= moon F m (k+3) i
   have hf: i<k+3:=by omega
   have hm:= (should he.blazing).protects k m i hf
   rw [cheek,playMinus]; change ‖jet (plays v-plays a) j x- jet (Y - T) j x‖ ≤ _; erw [Ion.jet_minus _ _ _ _ (froth_apt (lines_l w F (k:=k+3) (i:=i))) (froth_apt (anchor_d p R h (some (w+1)) i)),Ion.jet_minus _ _ _ _ (glowstar (should he.blazing) _ _ _ hf|>.analytic) (armor_apt p R h _),show jet Y j x=jet u j x from (nightwalk (glowstar (should he.blazing) _ _ _ hf|>.analytic) hm.analytic (survives hm) j (by omega) x)]
   unfold inkjet; rw [add_mul,show jet (plays v) j x-_ - (_-jet T j x)=jet (plays v) j x - jet u j x + (jet T j x- jet (plays a) j x) from ?_]; exact (norm_add_le ..).trans (add_le_add (tune_prices w he hg hw hf x) (silt p R hZ h (w+1) x i)); abel

variable {D:Stars→Side}(Q:∀ i:Stars,(D i).val=2*(ℓ+i.val))
def energy (k i:ℕ) :Story G:= hue (Model.clock Q (fun j=> anchor p R F (D j) k i))
omit hw he hg h
lemma taught (B:BudgetPoint): ∀ᶠ x:Link G n in 𝓝 0, flags B.threshold (input G n x)=∅:= by
   refine (show Tendsto (input G n) (𝓝 0) (𝓝 1) by simpa using (input_cont (G:=G) (m:=n)|>.tendsto 0)).eventually ((show ∀ᶠ x:Config G n in 𝓝 1,x∈Boulevard.sunny B from (Boulevard.sky B|>.mem_nhds ?_)).mono (fun _ h=> Boulevard.smoky h)); intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using B.threshold_pos

lemma appoint (Y:Story G)(B:BudgetPoint)(hc:4*r+16 ≤ c.val)(he:LocalOn (Lattice.box r) Y)(hr:Adapted Y)(hv:0<r)(hq:2*r≤ℓ)(k:ℕ)(x:Link G c): jet (plays (pass (hue (Model.clock Q (fun i=> froth (pass Y (D i))))) c)) k x=jet (plays (pass Y c)) k x:= by
   unfold jet; have hh:plays (pass (hue (Model.clock Q (fun i=> froth (pass Y (D i))))) c)=ᶠ[𝓝 0] plays (pass Y c):= by
      let y:=Y; have hx : ∀ s:Signed,∀ᶠ t: Link G c in 𝓝 0, flags B.threshold (pull s 0 (input G c t))=∅:= fun i=> (taught (G:=G) B ).mono fun t ht=> Meadow.covers_field (i,0) _ ht
      filter_upwards [eventually_all.mpr hx] with x ht; have h:=from_home Y (input G c x); rw [ice hr] at h; refine Eq.trans (from_home (Model.clock Q (fun i=> froth (pass Y (D i)))) _) ?_; exact (congr_arg (VerifiedReset.factor*·) (Finset.sum_congr rfl fun i _=> sideSum Y he hr hv (show ℓ+4≤ℓ+4 from le_rfl) hq hc B _ (ht i) Q)).trans h.symm
   rw [ (hh.iteratedFDeriv ℝ k).eq_of_nhds]
include hw he h hg
def upPrice (G:Gauge)(D : Stars→Side) (p:Clip)(Z μ C Λ A S:ℝ)(w k j:ℕ)(m:Side):ℝ:= inkjet G p Z μ C Λ A S w k j m + (Fintype.card (Site m):ℝ)*∑ i:Stars, ‖Slide.ray i‖*inkjet G p Z μ C Λ A S w k j (D i)
lemma transforms (hZ:PaintSupply G j Z) (B:BudgetPoint)(hc:4*(w+1)+16 ≤ m.val)(hy:3≤w)(ho:2*(w+1)≤ℓ)(x:L)(hi:j+i<k+3) : ‖jet (plays (pass (energy p R F Q (k+3) i) m)) j x - jet (anchor p R F m (k+3) i ∘ input G m) j x‖ ≤ upPrice (G:=G) D p Z μ C Λ A σ w (k+3) j m * ‖x‖^j:= by
   let v:= inkjet G p Z μ C Λ A σ w (k+3) j; let P:= anchor p R F; let Y:= cheek p R F w (k+3) i
   let T:= fun j=> anchor p R F (D j) (k+3) i; let V:= pass (energy p R F Q (k+3) i) m; let U:= fun i=> froth (pass Y (D i));
   let g i':= ‖Slide.ray i'‖ * v (D i'); let H:=(Fintype.card (Site m):ℝ) * ∑ i,g i; let h₁:=pass Y m;
   have hJ:0≤ H:= by
     have ht:=hw.nonneg; unfold H g v inkjet Model.pole; have hV:=sumFee_nn (G:=G) (μ:=μ) (C:=C) (Λ:=Λ) (k:=j) (Z:=outerCost G j Z) p; positivity
   let V₁:=pass (hue (Model.clock Q U)) m
   have hv(s:Signed): ‖jet (plays (pass (Model.clock Q T) m)) j (orderTurn s x)-jet (plays (pass (Model.clock Q U) m)) j (orderTurn s x)‖ ≤ H*‖x‖^j:= by
      let v':= orderTurn s x
      rw [adopts Q T (fun j=>anchor_apt p R F h he (by omega)), adopts Q U (fun j=>froth_apt (cheek_t p R F h w (k+3) i))]; unfold H; rw [mul_assoc]; apply averageFault _ _ ?_; intro y; rw [← sum_sub_distrib,Finset.sum_mul]; apply (norm_sum_le ..).trans (sum_le_sum (fun k hk=>?_))
      rw [←mul_sub,norm_mul,norm_sub_rev,mul_assoc]; -- g def
      let u:Link G (D k):= denial (Trio.pad Q k) y v'; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (abroad p R F h hw he hg hZ u hi w).trans; apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ _) ?_
      · exact ((denial (Trio.pad Q k) y).le_opNorm v').trans ((mul_le_of_le_one_left (norm_nonneg _) (nor_den (Trio.pad Q k) y)).trans (shape_invoice s x))
      have ht:=hw.nonneg; have hV:=sumFee_nn (G:=G) (μ:=μ) (C:=C) (Λ:=Λ) (k:=j) (Z:=outerCost G j Z) p; unfold inkjet Model.pole; positivity
   change ‖jet (plays V) j x- _‖ ≤ (v m+H)*‖x‖^j
   have hy': ‖jet (plays V) j x-jet (plays h₁) j x‖ ≤ H * ‖x‖^j := by
     rw [show jet (plays h₁) j x=jet (plays V₁) j x from (appoint Q Y B hc (stays p R F _ _ hy) (touches p R F) (by omega) ho _ x).symm]; erw [breeze (modulates Q T (fun j=>anchor_apt p R F h he (by omega))),breeze (modulates Q U (fun j=> froth_apt (cheek_t p R F h w (k+3) i)))]
     rw [← mul_sub, norm_mul,Real.norm_of_nonneg VerifiedReset.factor_pos.le]; exact ((mul_le_mul_of_nonneg_left (averageFault _ _ hv) VerifiedReset.factor_pos.le)).trans_eq (by rw [←mul_assoc, VerifiedReset.factor_card,one_mul])
   rw [add_comm (v m),add_mul]; apply (norm_sub_le_norm_sub_add_norm_sub (jet (plays V) j x) (jet (plays h₁) j x) _).trans; exact add_le_add hy' (abroad p R F h hw he hg hZ x hi w)
end YM.Contacts.Model
