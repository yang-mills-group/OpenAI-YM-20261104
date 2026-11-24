import YM.LocalTaylorR2.Exponent.Aura
import YM.LocalTaylorR2.Exponent.Barrio

/-!
 # Upgradeable mosaic.Bead. Revenue bought upfront for any symbols obeying (Off−eerie small bound at the SAME gauges & all atmos-frame derivatives) and enrolled.Ensemble. True Stella maps. Incl path.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open Axial Canvas Kiln Mesh Work.G05
-- nomination model: grade count log or inherited; p's own arguments polynomial inside vacuum.Aperture.One.G
-- exposed number of powers B.erase.
local notation "Mead"=> LogIndex c f → Port.Test T

def iceberg (H:Cash W s μ L Q o C T R)(p:ℕ)(i:LogIndex c f): Port.Test T:= match i with
| .inl (.inr (.inl i)) => demesne R (-Raw.orientation*R.beta) o.a R.path.cubic i (p+3)
| .inl (.inr (.inr (.inl i))) => demesne R (-Raw.orientation*R.beta) o.a R.path.quartic i (p+3)
| .inl (.inr (.inr (.inr (.inl i)))) => demesne R (-Raw.orientation) o.a R.path.loop i (p+3)
| .inr (.inl (.inl k)) => cub H p i +trunkInc H (p+2) k
| .inr (.inl (.inr (.inr k)))=> innerHa H p k
| _ => cub H p i
-- Corner overrides only at Owned Tall ticket; Propagator Φ.When χ_V lens.API.

structure Hallmarked (H:Cash W s μ L Q o C T R)(Φ Δ: LogIndex c f→Port.Test T)(j p:ℕ)(ζ w D v d:ℝ)(χ:Chi):Prop where
  vivre : ∃ f':LogIndex c f→ℝ, Sales (radiusB s) Q.relative Q.ε (roadway T R (radiusB s) Q.halo) (fun i=>betaF G s L^leaseLog ζ c _ i* f' i) (exCharge T R) w ∧ ∀ i,
    Astonish H (H.supportP (identityLog i)) j p v d χ (f' i*D) (spanW T R (radiusB s) Q.halo (identityLog (S:=S) i)) (Δ i-Φ i)
-- Actual post-calendaring always obtains.
structure Observatory (G:Gauge) extends Regime G where
  upgrade : ∀ {c f L : Side}{S:StepData c f}{T:Tube G S}{R:Rep G f}{P:Teller G}{Q:YM.ConnectedActivityE6.Target G P}{W x μ C:ℝ}{o:Target.Order G W}, Cash W x μ L Q o C T R → ℕ → LogIndex c f → Port.Test T
  evolve : ∀ (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P),∃ k :ℕ,∀ (L:Side), k≤L.val → ∀ (D:Patch),D.Branches P.bind G → ∀ (p j:ℕ)(χ:Chi)(W:ℝ)(o:Target.Order G W)(ζ θ:ℝ),-(1/2:ℝ)<θ → ∀ (v d:ℝ→ℝ), Rate G L (-(1/2)) v → Rate G L (-(1/2)) d → (∀ᶠ x in atTop,0≤ v x) → ∃ w e t k, Rate G L t w ∧ Rate G L θ e ∧ ∀ᶠ x in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(R: Rep G f)(μ C:ℝ)(H:Cash W x μ L Q o C T R), S.patch=D→ Stamp T → (∀ i, Kept H (H.supportP (identityLog i)) (symbol H p i)) → Hallmarked H (symbol H p) (upgrade H p) j k ζ (e x) (|w x|) (v x) (d x) χ

private lemma sine (χ:ℝ)(P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(b:ℝ)(hχ:χ≤1/2)(hz:-(1/2:ℝ)<b)(d:ℕ){τ:ℝ→ℝ}(h:Rate G L 0 τ): let v x:= betaF G x L ^ (-(2:ℝ)); ∀ᶠ x in atTop, ∀ (c f:Side)(S:StepData c f), S.patch.L = L → ∀ T:ℕ→Atom G d, SumBudget (fun i=>(T i).budget P.top.width) (τ x) → ∀ (η:ℝ), |η|≤2*betaF G x L → Sales (radiusB x) Q.relative Q.ε (atomFoot S.ratio Q.halo (radiusB x) T) (fun i=> (betaF G x L)^χ * Kiln.bill (v x) 0 η x T i) (atomCharge T) (betaF G x L^b):=by
  intro v; have he:=Q.grants.2.1; have hv : Rate G L (-((0+4:ℕ):ℝ)/2) v:= by norm_num; convert (Rate.power (a:=-(2:ℝ)))
  have hb:= Kiln.shops G L Q.halo 0 d P.top.width _ _ Q.usable (show 0 ≤ Q.relative from (by unfold Target.relative;linarith [Q.usable,Q.bound,Q.pos])) he hv (Rate.const (0:ℝ)) h 0 χ b (by norm_num) hχ hz
  simpa only [pow_zero,mul_one] using hb

lemma stricture (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(ζ θ:ℝ)(D:Patch)(hD:D.Branches P.bind G)(p j:ℕ)(χ:Chi)(o:Target.Order G W)(ht:-(1/2:ℝ)<θ)(v d:ℝ→ℝ)(hv:Rate G L (-(1/2)) v)(hd:Rate G L (-(1/2)) d)(hp:∀ᶠ x in atTop,0 ≤ v x) : ∃ w e, Rate G L 2 w ∧ Rate G L θ e ∧ ∀ᶠ x in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(R:Rep G f)(μ C:ℝ)(H:Cash W x μ L Q o C T R), S.patch=D→ Stamp T → (∀ i, Kept H (H.supportP (identityLog i)) (cub H p i)) → Hallmarked H (cub H p) (iceberg H p) j (p+3+j) ζ (e x) (|w x|) (v x) (d x) χ := by
  choose b hb h using fun n=> protege P L o (p+3) j n χ D hD v d hv hp hd
  obtain ⟨K,hK,hΨ⟩:= commonAnnual P L o χ (p+2) j D hD v d hv hp hd
  obtain ⟨B,hB,hΩ⟩:= outerlaw P Q L o χ j p d hd
  let X₁ x:= |b 2 x| + |b 3 x| + |b 4 x|; let k:= -(1/2:ℝ); let t x:= betaF G x L; let e x:= t x^k; let w x:= t x^2 *X₁ x +(t x^(1/2:ℝ))*(|K x|+|B x|)
  have he {a b} (_ : ℝ) (h:Rate G L a b):= h.compare (v:=fun x=>|b x|) (Eventually.of_forall fun t=>(abs_abs _).le)
  have hχ:= (he 0 hB).weaken (b:=1) (by norm_num); have hS : Rate G L 2 w :=by
     apply Rate.add
     · exact (((Rate.hat.pow 2).mul (((he 0 (hb 2)).add (he 0 (hb 3))).add (he 0 (hb 4)))).weaken (by norm_num))
     exact (Rate.power.mul ((he 0 hK).add hχ)).weaken (by norm_num)
  let m:= Fintype.card Signed*Census.spots L+(Itinerary.density L+ Itinerary.density L)
  let d₁ x:= (ballCost ((Q.halo+1)*radiusB x):ℝ)*m*(e x*Real.exp (Q.relative*ballCost (Q.halo+1)))
  have hV:=Census.width_rate G L (Q.halo+1) 0; simp only [add_zero] at hV
  refine ⟨w,fun x=>t x^θ*3+d₁ x,hS,(Rate.power.mul_right 3).add ( ((hV.mul_right m).mul ((Rate.power (a:=k)).mul_right _)).weaken (by unfold k; linarith)),?_⟩
  filter_upwards [sine 0 P Q L θ (by norm_num) ht 3 (Rate.const P.top.paths), sine (1/2) P Q L θ le_rfl ht 4 (Rate.const P.top.paths), sine (1/2) P Q L θ le_rfl ht 2 (loopBill_rate G L), h 3,h 4,h 2,hΨ,hΩ,Delay.shift_pos G L] with x h₃ h₄ h₂ H₃ H₄ H₂ hy hh hy' c f S T R μ C H hD hT ha
  have hP:= H.laws.data; have htX:=hP.room; have ht:= hP.funds.length_eq; have hQ:=H.laws.intake; have hR:=hQ.cap.paths; have hz:0≤Q.relative:=by unfold Target.relative;linarith [Q.usable,Q.bound,Q.pos]
  have hE:0≤ e x:= (Real.rpow_pos_of_pos hy' _).le
  let g:= -Raw.orientation; let ℓ := g*R.beta; have hb : 1 ≤ betaF G x L:= by rw [← ht]; exact hQ.height.le
  have hg:|g|≤1:= by unfold g; rw [abs_neg,abs_of_nonneg orientation_range.1.le]; exact orientation_range.2
  have hp':|ℓ|≤2*betaF G x L:=by rw [show |ℓ|=|g| * R.beta by unfold ℓ; rw [abs_mul,abs_of_nonneg hQ.positive.le],←ht]; exact (mul_le_of_le_one_left hQ.positive.le hg).trans hQ.window.2
  let f' :∀{j},(A:ℕ→Atom G j)→ℝ→Trans f→ℝ:= fun {j} A η i=> Kiln.bill (t x ^(-(2:ℝ))) 0 η x A i
  let γ:LogIndex c f→ℝ:=Sum.elim (Sum.elim (fun _=>0) (Sum.elim (f' R.path.cubic ℓ) (Sum.elim (f' R.path.quartic ℓ) (Sum.elim (f' R.path.loop g) (fun _=>0))))) (Sum.elim (fun _=> e x) (fun _=>0))
  refine ⟨γ,?_,fun i=>?_⟩
  · let d':=t x^θ; have hF:= YM.ConnectedActivityE6.fixed (ε:=Q.ε) (C:=e x) (smallCensus S L ht) (show 0<radiusB x from lt_of_lt_of_le (by norm_num) htX.sight.1) _ (packed S (l:=Q.halo) (lt_of_lt_of_le (by norm_num) htX.sight.1)) hz hE
    rw [ht] at hR
    have h0:=h₃ _ _ S ht _ hR.three ℓ hp'; have h1:= h₄ _ _ S ht _ hR.four ℓ hp'; have h2:=h₂ _ _ S ht _ hR.two g (by linarith)
    rw [show t x^θ*3+d₁ x=0+(d'+(d'+(d'+0)))+(d₁ x+0) from by unfold d'; ring]; convert ((free (regularFoot S.ratio Q.halo (radiusB x) R) (regularExtra R) (radiusB x) Q.relative Q.ε).together (h0.together (h1.together (h2.together (Mesh.free (Sum.elim (bothFoot S.ratio Q.halo (radiusB x) R.path) (bothFoot (atOne c) Q.halo (radiusB x) T.down)) (Sum.elim (bothCharge R.path) (bothCharge T.down)) (radiusB x) Q.relative Q.ε))))).together (hF.together (Mesh.free (basisFoot S (radiusB x) Q.halo) (basisCharge f) (radiusB x) Q.relative Q.ε)) using 1
    · rfl
    · funext i; rcases i with (i|(i|(i|(i|(i|i)))))|i|i <;> try rfl
      all_goals simp only [γ,Sum.elim, leaseLog, leaseRaw,mul_zero,Real.rpow_zero,one_mul]
    rfl
  have hs (n:ℕ)(h':|b n x| ≤ X₁ x) (i:Trans f)(A:ℕ→Atom G n)(η:ℝ): Kiln.bill (b n x) 0 η x A i≤ f' A η i*|w x| :=by
     rw [weighs n _ η (t x) hy']; apply mul_le_mul_of_nonneg_left _ (positiveBill ..); apply le_trans _ (le_abs_self _); unfold w; have hv:=Real.rpow_nonneg hy'.le (1/2:ℝ); unfold t; exact le_trans (mul_le_mul_of_nonneg_left h' (sq_nonneg _)) (le_add_of_nonneg_right (by positivity)) -- gcongr doesn't? need through le_add
  have hv : t x ^ (1/2:ℝ)*(|K x|+|B x|) ≤ |w x|:= by apply le_trans _ (le_abs_self _); unfold w X₁; exact le_add_of_nonneg_left (by positivity)
  have hf: |K x|+|B x|≤ e x *|w x|:= by
     let s :ℝ:=1/2; have ht0:e x=(t x^s)⁻¹:=Real.rpow_neg hy'.le _; rw [ht0]; apply le_trans _ (mul_le_mul_of_nonneg_left hv (ht0 ▸ hE)); apply le_of_eq; rw [← mul_assoc,inv_mul_cancel₀ (Real.rpow_pos_of_pos hy' s).ne',one_mul]
  have hq i : 1≤ spanW T R (radiusB x) Q.halo (identityLog (S:=S) i):= le_add_of_nonneg_right (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rcases i with (i|(i|(i|(i|(i|i)))))|i|i
  · simp_rw [iceberg,sub_self]; exact Astonish.null (zero_le_one.trans (hq _)) (mul_nonneg (le_refl (0:ℝ)) (abs_nonneg _))
  · exact (H₃ _ _ S T R Q μ C H hD hT _ _ i (hR.invariant _).2.1 (ha (.inl (.inr (.inl i))))).raises le_rfl le_rfl (hs 3 (by unfold X₁; linarith [abs_nonneg (b 4 x),abs_nonneg (b 2 x)]) _ _ _) (positiveBill ..) -- ha need explicit index
  · exact (H₄ _ _ S T R Q μ C H hD hT _ _ i (hR.invariant _).2.2 (ha (.inl (.inr (.inr (.inl i)))))).raises le_rfl le_rfl (hs 4 (by unfold X₁; linarith [abs_nonneg (b 2 x),abs_nonneg (b 3 x)]) _ _ _) (positiveBill ..)
  · exact (H₂ _ _ S T R Q μ C H hD hT _ _ i (hR.invariant _).1 (ha (.inl (.inr (.inr (.inr (.inl i))))))).raises le_rfl le_rfl (hs 2 (by unfold X₁; linarith [abs_nonneg (b 3 x),abs_nonneg (b 4 x)]) _ _ _) (positiveBill ..)
  all_goals try simp_rw [iceberg,sub_self]; exact Astonish.null (zero_le_one.trans (hq _)) (mul_nonneg (le_refl (0:ℝ)) (abs_nonneg _))
  rcases i with i|i|i
  · rw [iceberg,add_sub_cancel_left]; exact (hy _ _ S T R Q μ C H hD i).raises (by omega) (hq _) ((le_add_of_nonneg_right (abs_nonneg (B x))).trans hf) (abs_nonneg _)
  · simp_rw [iceberg,sub_self]; exact Astonish.null (zero_le_one.trans (hq _)) (mul_nonneg hE (abs_nonneg _))
  exact (hh _ _ S T R μ C H _ _).raises (by omega) (hq _) ((le_add_of_nonneg_left (abs_nonneg (K x))).trans hf) (abs_nonneg _)

def astrolabe (G:Gauge): Observatory G where
 toRegime:= resting G
 upgrade H p i:=iceberg H p i
 evolve P Q:=by
   refine ⟨0,fun L _ D hD p j χ W o ζ θ ht v d hv hd hp=>?_⟩
   obtain ⟨w,b,hw,hb,h⟩:= stricture P Q L ζ θ D hD p j χ o ht v d hv hd hp
   exact ⟨w,b,2,p+3+j,hw,hb,h⟩
end YM.LocalTaylorR2.Exponent
