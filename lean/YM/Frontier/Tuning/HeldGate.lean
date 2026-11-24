import YM.Frontier.Tuning.Held
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Flotsam
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plateau

/-! Locality on the inherited palette, before selecting score determinants. No admissibility of the COMPLEX combined argument should be assumed or needed to switch chart entries. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.Frontier.Tuning.HeldGate
open Held
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k k':Finset ℕ} {R A : Rep G f} {X : Coat T F} {e f':Payload G f} {l : ℕ}
variable {a W : ℝ}{τ:ℂ}{u u':Directions G f}{I I':Config G f}
variable {O:ChartRatio G}
variable {x y : Air f G}{Y : Support c}
lemma selfFacing (hR:0<R.beta) (b:ℝ)(hb:0<b): Facing R {R with beta:=b}:= ⟨rfl,rfl,rfl,rfl,rfl,hR,hb⟩

/-- Extract the penalized log difference *only* on a live stock. -/
lemma termAlign (hR:0<R.beta)(j:Stores S)
 (hV:∀ (A:Rep G f),A=R ∨ A={R with beta:=R.beta+1} → stock X a A W O u I k j=stock X a A W O u' I' k' j) :
 (penGain X R I u O τ j) * (stock X a R W O u I k j:ℂ)=(penGain X R I' u' O τ j) * (stock X a R W O u' I' k' j:ℂ):=by
  classical
  let A : Rep G f := {R with beta:=R.beta+1}
  have hb:= hV R (.inl rfl); by_cases h : stock X a R W O u I k j=0
  · rw [← hb,h]; simp only [Complex.ofReal_zero,mul_zero]
  have hA:=hV A (.inr rfl)
  have hf : Facing R A:= selfFacing hR _ (by linarith)
  rw [stockMoon a W hf,stockMoon a W hf,← hb] at hA
  replace hA:=Real.exp_injective (mul_left_cancel₀ h hA)
  have hc : A.beta=R.beta+1:=rfl
  have hq : chalky X u I j=chalky X u' I' j:= by rw [hc] at hA; linarith only [hA]
  unfold penGain; rw [hb,hq]

variable {r s p q : ℂ} (ho : ∀ i y,e i y =r*R.activities.E i y+s*A.activities.E i y)
      (ht : ∀ i y, f' i y=p*R.activities.K i y+q*A.activities.K i y) (hf : Facing R A)
variable (hr : Intake P T X.x R) (ha : Intake P T X.x A) (hk : Room P S T X.x)
include ho ht hf hr ha hk
set_option maxRecDepth 4000 in
lemma reel (H:Armor X a u I I') (i : Head S): emberC X R I u x O a W k τ l e f' i = emberC X R I' u x O a W k τ l e f' i:=by
  rcases i with j|j|j|j
  · simp only [emberC,Sum.elim]; split_ifs; swap; · rfl
    exact termAlign hf.pos _ (fun C _=> H.bast hk k W C O j)
  · rw [mix_K X R I u x O _ _ _ _ A ht hf, mix_K X R I' u x O _ _ _ _ A ht hf]
    suffices he : ∀ B : Rep G f, Intake P T X.x B → sheath X a B u I j=sheath X a B u I' j by rw [he R hr,he A ha]
    intro B hh; exact H.reeled hk W O k l hh (.inr (.inl j)) x -- check order
  · change Complex.exp (comboLog _ _ _ _ _ _ _ _ _ j)-1 = Complex.exp (comboLog _ _ _ _ _ _ _ _ _ j)-1
    apply congr_arg (fun x:ℂ=> Complex.exp x-1)
    have HZ (B:Rep G f)(hB:Intake P T X.x B) : logMoment X a B O u I x j=logMoment X a B O u I' x j := by
      apply Real.exp_injective; apply eq_of_sub_eq_zero (?_)
      have hw: Real.exp _ - 1 = Real.exp _ - 1:= H.reeled hk W O k l hB (.inr (.inr (.inl j))) x
      exact sub_eq_zero_of_eq (sub_left_inj.mp hw)
    rcases j with (j|j)|j
    · rw [mix_log X R I u x O _ _ A ho hf,mix_log X R I' u x O _ _ A ho hf,HZ R hr,HZ A ha]
    all_goals simp only [comboLog,HZ R hr]
  · exact _root_.congrArg Complex.ofReal (H.reeled hk W O k l hr (.inr (.inr (.inr j))) x)
omit ho ht hr ha hk in
lemma area_eq : Matter.areas R T l X.B=Matter.areas A T l X.B:=by unfold areas footprints forcedFoot roadway; rw [hf.forced]; rw [location hf (n:=X.B) (l:=l) (T:=T)]
include ho ht hf hr ha hk

set_option maxRecDepth 8000 in
lemma preserve (H:Borough X X Y x y k k R) (hzl : 500 ≤ l) (i : Head S)
   (hi : areas R T l X.B i⊆ Y):
    let w:=worldZ X R.beta x; let v:=worldZ X R.beta y
    emberC X R (X.input w) w x O a W k τ l e f' i = emberC X R (X.input v) v y O a W k τ l e f' i:=by
  intro w v
  classical
  let I:=X.input w; let I':=X.input v
  change emberC _ _ I _ _ _ _ _ _ _ _ _ _ _ = emberC _ _ I' _ _ _ _ _ _ _ _ _ _ _
  have hv (B:Rep G f) (g:Facing R B) (hh: Intake P T X.x B): ember X a B W O w I (low R B•x) k l i=ember X a B W O v I' (low R B•y) k l i:=by
     have hAir (i:Tubular f G) (hi : i∈podium S G Y X.B) : (low R B • x).ofLp i=(low R B • y).ofLp i:=by
       change low R B * x.ofLp i=low R B * y.ofLp i; rw [show x.ofLp i=y.ofLp i from H.airs i hi]
     have hV : Borough X X Y (low R B • x) (low R B • y) k k B:=⟨H.toVillage,hAir,fun i hi=>Iff.rfl⟩
     have hz:areas B T l X.B i⊆Y:= by rw [← area_eq (X:=X) g]; exact hi
     have he:= (hV.rooms hk B.beta).preserve hk (l:=l) ‹_› hh a W O (i:=i) hV hz
     dsimp only at he
     simp_rw [Coat.oldysis _ hh.positive,moving g] at he
     exact he
  have Id : Facing R R := ⟨rfl,rfl,rfl,rfl,rfl,hf.pos,hf.pos⟩
  have hu:low R R=1:= div_self (show Coat.gStep R.beta ≠ 0 from (inv_pos.mpr (Real.sqrt_pos.mpr hf.pos)).ne')
  rcases i with j|j|j|j
  · simp only [emberC,Sum.elim]; split_ifs; swap; · rfl
    apply termAlign hf.pos j; intro B hb
    suffices g:Facing R B by
      have hAir (i:Tubular f G) (hi : i∈podium S G Y X.B) : (low R B • x).ofLp i=(low R B • y).ofLp i:=by
        change low R B * x.ofLp i=low R B * y.ofLp i; rw [show x.ofLp i=y.ofLp i from H.airs i hi]
      have hV : Borough X X Y (low R B • x) (low R B • y) k k B:=⟨H.toVillage,hAir,fun i hi=>Iff.rfl⟩
      have he:= (hV.rooms hk B.beta).towering (A:=j) hk (Subset.trans (Lattice.Corona.halo_mono (Nat.mul_le_mul_right X.B hzl) (Subset.refl j.place)) hi) O a W
      dsimp only at he
      simp_rw [Coat.oldysis _ g.pos',moving g] at he
      exact he
    rcases hb with rfl|rfl
    exact Id
    exact selfFacing hf.pos _ (by linarith only [hf.pos])
  · rw [mix_K X R I w x O _ _ _ _ A ht hf, mix_K X R I' v y O _ _ _ _ A ht hf]
    rw [show sheath X a R w I j=sheath X a R v I' j from hv R Id hr,show sheath X a A w I j=sheath X a A v I' j from hv A hf ha]
  · change Complex.exp (comboLog _ _ _ _ _ _ _ _ _ j)-1 = Complex.exp (comboLog _ _ _ _ _ _ _ _ _ j)-1
    apply congr_arg (fun x:ℂ=> Complex.exp x-1)
    rcases j with (j|j)|j
    · rw [mix_log X R I w x O _ _ A ho hf,mix_log X R I' v y O _ _ A ho hf]
      have hs (B:Rep G f) (g:Facing R B) (hh: Intake P T X.x B): logMoment X a B O w I x (.inl (.inl j))=logMoment X a B O v I' y (.inl (.inl j)):=by
        exact Real.exp_injective (sub_left_inj.mp (hv B g hh))
      rw [hs R Id hr,hs A hf ha]
    all_goals
      have he:=hv R Id hr; rw [hu,one_smul,one_smul] at he
      exact congr_arg (fun h:ℝ=> ((if flips c f _ then τ/R.beta else 1:ℂ)*↑h)) (Real.exp_injective (sub_left_inj.mp he))
  · specialize hv R Id hr; rw [hu,one_smul,one_smul] at hv; exact congr_arg Complex.ofReal hv
lemma coast (H:Borough X X Y x y k k R) (hzl : 500 ≤ l) (i : Molecule S)
   (hi : ground R T l X.B i⊆Y): floatC X R x O a W k τ l e f' i=floatC X R y O a W k τ l e f' i:= by
  apply Finset.prod_congr rfl; intro z hz
  exact preserve ho ht hf hr ha hk H ‹_› z (Subset.trans (Finset.subset_biUnion_of_mem (areas R T l X.B) hz) hi)
end YM.Frontier.Tuning.HeldGate
