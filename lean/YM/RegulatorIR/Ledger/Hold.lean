import YM.RegulatorIR.Ledger.Hue
import YM.RegulatorIR.Ledger.Ori

/-! Fine-side growth cost (source testing in reporting units) and period
split. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type}{M:W→ℕ}{X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts) {m:ℕ}(Z:T.Report m)
variable {k j : Choice M}{γ:ℝ}{p b h α e r u:ℕ}{x: W→Room}{L:Meter W}{c:Flap M→ℝ≥0∞}{s:W→ℝ≥0∞}

def Preserved (s:W→ℝ≥0∞)(h:ℕ)(p:ℕ)(k:Choice M)(x:W→Room)(u:ℕ)(L: Meter W): Prop := let E:= k.before;
   ∀ i ≤ p,∀ j, Claim (coverL E.spans L) (fun w=> S.coverQ x u (E.page w)) (fun w=> ENNReal.ofReal ((S.l (E.page w)^h)⁻¹) * s w.bindW) fun w=> Z.main (E.page w) i j

lemma prevails (R: S.Radiants L γ b α c k)(P:S.Preserved T Z s h p k x u L) (he:e ≤ p): Claim L (fun w=>S.coverQ x u (k.choose w)) s fun w=> Z.main (k.choose w) e r := by
 let E:= k.before
 have he' : Carry L (fun w=> ENNReal.ofReal ((S.l (k.before.page (k.lastPage w))^h)⁻¹)*s w) fun w=> markQ (S.coverQ x u (k.before.page (k.lastPage w))) (Z.main (k.before.page (k.lastPage w)) e r):= Carry.us (P e he r) k.lastPage
 unfold Claim; convert he' using 1
 · ext1 w; rw [Choice.meet,R.ref_mesh]; simp
 ext1 w; rw [Choice.meet]

lemma appear (R:S.Radiants L γ b α c k)(P:S.Preserved T Z s h p k x u L) (H:∀ w i,i≤p → (S.sight w).Way (Z.main w.prev) i)
  (hh:∀ w i j,i≤ p → 0<j → j < α → Z.main w i j=0)(hv:∀ w,s w ≠ ⊤): S.Bend T Z u p k x (S.softnessWeight γ) s α L:= by
 refine ⟨fun i hi j _=> ?_, H, hh,hv⟩
 convert S.prevails T Z R P hi using 1; ext1 w; rw [ticket,softnessWeight,R.ref_mesh];simp [Choice.choose]

lemma weld (R:S.Radiants L γ u α c k)(N:S.Primitive L p b)(P:S.Preserved T Z 1 h p k x u L)(B:S.Supplies T L p b)
  (H: S.Bend T Z u p k x (S.softnessWeight γ) 1 α L)(hu:u ≤ b) (he:e≤ p)(hr:0<r): Claim (flapL M L) (S.yard x u) (S.priceStep h γ k) (fun w=> Z.main w.prev e r):= by
 let E:= k.before; let E':= k.after; let D:= E.expanse S; let F:= E'.expanse S
 let f(w:Flap M):= markQ (S.yard x u w) (Z.main w.prev e r)
 have hh: Carry (flapL E.spans L) (fun w=> S.priceStep h γ k (E.wing w)) fun w=>f (E.wing w):= by
   have H' : Claim (coverL E.spans L) (D.coverQ x u) (fun w=> ENNReal.ofReal ((D.l w^h)⁻¹)*1) fun w=> Z.main (E.page w) e r:= P e he r
   have he:= D.prior _ H'; unfold Claim at he; convert he  using 1 <;> try rfl
   ext1 w
   have hh:w.offset<k.age w.volW:= w.ok; rw [priceStep,if_neg]; change _=ENNReal.ofReal _ * 1; rw [mul_one]; rfl
   change ¬ k.age w.volW≤ 0+w.offset; omega
 have hz: Carry (flapL E'.spans L) (fun w=> S.priceStep h γ k (E'.wing w)) fun w=> f (E'.wing w):= by
   have he' : Claim (coverL E'.spans L) (F.coverQ x u) (fun w=> ticket (S.softnessWeight γ) 1 (E'.page w)) fun w=> Z.main (E'.page w) e r:= S.apogee T Z N B (S.warmer R) H hu he hr
   have hx:= F.prior _ he'; unfold Claim at hx; convert hx using 1 <;> try rfl
   ext1 w
   have hh : 0<S.l (E'.wing w).prev:= S.hl _
   rw [priceStep,if_pos (show k.age (E'.wing w).volW ≤ (E'.wing w).offset from Nat.le_add_right (k.age w.volW) _)]
   change ENNReal.ofReal _ = 1*(ENNReal.ofReal (S.l (E'.wing w).prev ^ γ))⁻¹; rw [ENNReal.ofReal_inv_of_pos (by positivity), one_mul]
 obtain ⟨f',⟨c,j,hc,Hc⟩,L'⟩:=hh; obtain ⟨g',⟨d,k',hd,Hd⟩,D'⟩:=hz
 refine ⟨_,Poly.add ((Poly.standard (flapL M L) hc).mul ((Poly.roof _).powQ j)) ((Poly.standard (flapL M L) hd).mul ((Poly.roof _).powQ k')),?_⟩
 intro w
 rcases lt_or_ge w.offset (k.age w.volW) with hv|hv
 · obtain ⟨w,rfl⟩:= Radiants.front _ hv
   apply (L' w).trans
   exact mul_le_mul_left ((Hc w).trans (le_add_right le_rfl)) _
 obtain ⟨w,rfl⟩:=Radiants.rearward _ hv
 apply (D' w).trans
 exact mul_le_mul_left ((Hd w).trans (le_add_left le_rfl)) _
end YM.RegulatorIR.Ledger.Sky
