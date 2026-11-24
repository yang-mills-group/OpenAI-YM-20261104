import YM.LocalLTE.FieldPT.Affine
/-!
 Curvature reset interpretation all virtual couplings before projection. Main terms
 `axes` kept in unmasked realization, support costs via actual envelope.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {W U C V: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{p:ℝ→E→ℝ}
-- k paid; projection-to-axes uses valence
lemma shadings (k d:ℕ) (he:Hex j p)(hp:∀ i∈Weft.clip,Null k d (p i)) (hf:∀ s∈Weft.clip, Brush d U 1 (fun v=> s^k*p s v) 0) : Arp j d U p:= by
   refine ⟨he,fun i hi=>?_⟩; let f(x:E):= i^k*p i x
   have hh : Null k d f:=by
       intro j' hj hh; have ht:= hf _ hi
       have hz: p i=(fun x=> (i^k)⁻¹*f x):=funext fun x=> by unfold f; have hp:0 < i:=hi.1; field_simp
       have hD:ContDiffAt ℝ (↑j') (p i) 0:= by rw [hz]; exact contDiffAt_const.mul (ht.smaller hj|>.smooth) -- edit
       change iteratedFDeriv ℝ j' (fun x=> (i^k) • p i x) 0=0; rw [iteratedFDeriv_const_smul_apply' hD,hp _ hi _ hj hh,smul_zero]
   apply ((Arp.reduced (h:=hf _ hi) hh|>.brush i hi)).shimmy; apply Eventually.of_forall; intro x; change p i _=(i^k)⁻¹ * (i^k *p i _); rw [inv_mul_cancel_left₀ (pow_ne_zero _ hi.1.ne')]
end
variable {G}
lemma shaded (hG:G.Simple) {g:Config G n→ℝ} {p:BudgetPoint} {x:RegularAddress n} (hp:p.Regular x.support g)(he:g 1=0)(i:ℕ) : Null 2 i (g ∘ Grove.soloV):=by
    intro j h hj; apply norm_le_zero_iff.mp; rcases (show j=0∨ j=1 from by omega) with h|h <;> subst j
    · rw [norm_iteratedFDeriv_zero,Function.comp_apply,Hall.zeroSolo,he,norm_zero]
    rw [norm_iteratedFDeriv_one, ← Hall.bare,show fderiv ℝ (g ∘ increment 1) 0=0 from flat_critical hG hp,norm_zero]
section shell
variable {p: BudgetPoint} (hG:G.Simple) (a:RegularAddress n) {A:ℝ→ Config G n→ℝ}
include hG
lemma pickC (f:ℝ→ Config G n→ℝ) (he: ∀ i l, Hex j (fun s=> projection a (f s) i l)∧∀ s∈Weft.clip, |s^2 * projection a (f s) i l|≤ C) (p:BudgetPoint)(hr:∀ s∈Weft.clip,p.Regular a.support (f s))(n':ℕ) (hg : ∀ (q:PlaqAxes→PlaqAxes→ℝ)(u:ℝ), (∀ i j,|q i j|≤u) → Brush n' (u*W) 1 (counter q a.site (G:=G) ∘ Grove.soloV) 0 ) : Arp j n' (C*W) (fun s=> Residual.payout a (f s) ∘ Grove.soloV):=by
    let v s := projection a (f s); let w(s:ℝ)(i:PlaqAxes→G.Color):=quad (v s) i i
    have hv k: Hex j fun s => w s k := by
       unfold w quad v; simp_rw [show ∀ s i j, projection a (f s) i j * inner ℝ (k i) (k j) = inner ℝ (k i) (k j)* projection a (f s) i j from fun s i j=> mul_comm ..]; exact Hex.total Finset.univ fun i hi=> Hex.total Finset.univ fun l hl=> (he i l|>.1).oneZ _
    have hh k: Hex j fun s =>w s k/2:= by
       simp_rw [div_eq_inv_mul]; exact (hv k).oneZ _
    refine shadings 2 n' (Hex.invert (fun i=>hh (petals _ _))) (fun i hi=>shaded hG (x:=enlarges a) (payout_regular a (hr _ hi)) (by simp [payout,counter,quad]) n') (fun s hs=> ?_)
    have hp':=hg (s^2 • v s) C (fun i l=>he i l|>.2 s hs)
    exact hp'.shimmy (Eventually.of_forall (fun i=> (by unfold payout counter quad; simp only [Function.comp_apply,v,Pi.smul_apply,smul_eq_mul,← mul_div_assoc, mul_assoc,Finset.mul_sum]
        )))
omit hG in
lemma dollar (o:Site n)(a:Grove o)(x:ℝ→ℝ)(h:Hex j x)(k l:ℕ)(κ:ℝ)(he:∀ i∈Weft.clip, |x i|≤W) : Scene (G:=G) a κ l j (k+1) (fun t=> Function.const _ (x t)) W:= by
    let f t (i:Directions G n):= x t
    have hp' : Arp j (k+1) W f:=⟨Hex.invert (fun _=>h), fun i hi=> (Brush.certified zero_le_one _).climb (he _ hi) le_rfl⟩; apply (Scene.spinner _ a _ _ hp' le_rfl).change; -- edit
    intro s hs; funext v; change Cabana.actual (FrameBox.colorP (Hall.bushes (k+1) (fun _:Config G n=>x s))) _=_; rw [FrameBox.sunwheel]; simp_rw [Hall.bays]; -- stem read
    have hz (A:Directions G n): LocalLTE.stem (k+1) (fun _:Directions G n=> x s) A=x s:=by
      unfold LocalLTE.stem; rw [Finset.sum_apply,Finset.sum_eq_single (0:ℕ)]; · change Tensor.coeff (fun _:Directions G n=>x s) 0 _ _=_; rw [Tensor.coeff_apply_zero]
      · intro j hj he; unfold Tensor.diagonal Tensor.coeff; rw [iteratedFDeriv_const_of_ne he, Pi.zero_apply,smul_zero]; rfl
      simp
    change (∫ u:G.El, LocalLTE.stem (k+1) (fun _:Directions G n=> x s) _ ∂G.probHaar)= _; simp_rw [hz]; simp
-- component hull.Public
variable {l z:ℕ}(F:Art a z){κ K:ℝ}(n' j:ℕ) (hp: Reliable G κ K) (he: Weft.Scene F.grove κ F.radius j (pie n'+1) A C)(hr:∀ s∈Weft.clip, p.Regular a.support (A s))
include he hr
lemma capBudget (hg:Arp j 2 W (fun s=> A s ∘ Grove.soloV))(hf:∀ (q:PlaqAxes→PlaqAxes→ℝ)(u:ℝ), (∀ i j,|q i j|≤u) → Brush (pie n'+1) (u*V) 1 (counter q a.site (G:=G) ∘ Grove.soloV) 0) : Scene F.grove κ F.radius j (pie n'+1) (fun s=>myth F (A s) κ n') ((C+W)+(W*(z:ℝ)^2*V)):= by
    have hz: ∀ i∈Weft.clip, |A i 1| ≤ W:=by intro i hi; have he:=hg.brush i hi|>.bound; simpa only [smul_zero, Function.comp_apply,Hall.zeroSolo] using! he
    exact (he.lyric (Price.dollar a.site F.grove _ (he.weft.use 1) (pie n') _ _ hz)).lyric (Scene.spinner (pie n'+1) _ _ _ (Price.pickC hG a A (fun i j=> Scene.implies hG a i j ((show soloV (G:=G) (c:=n)=increment 1 from Hall.bare.symm) ▸ hg) (by rw [F.crisp]) hr) p hr (pie n'+1) hf) le_rfl)

end shell
end YM.AnalyticBridge.VerifiedReset.Collection.Price
