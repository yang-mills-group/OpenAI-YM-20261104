import YM.LocalLTE.Roost.Port
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
-- Currency to E producer.
namespace Pastel
def chip (q:ℕ):ℝ:= -(11/10:ℝ)-(q:ℝ)/100
def pie (q:ℕ):= 8+q
def mini:ℝ:= -(3/8:ℝ)
def slack:ℝ:=1/1000
end Pastel
open Pastel
-- separate true β (reweighted) vs independent output perturb amplitudes. Small logarithms only here.
abbrev Veil (c f : Side):Type:= ℕ ⊕ Trans f ⊕ Trans f ⊕ Trans f ⊕ Miniature c f
def chapter : Veil c f→ LogIndex c f:= Sum.elim (fun i=>.inl (.inl i)) (Sum.elim (fun i=>.inl (.inr (.inl i))) (Sum.elim (fun i=>.inl (.inr (.inr (.inl i)))) (Sum.elim (fun i=> .inl (.inr (.inr (.inr (.inl i))))) (fun i=>.inr (.inl i)))))
lemma padded : Injective (chapter (c:=c) (f:=f)):=by rintro (i|i|i|i|i) (j|j|j|j|j) <;>simp [chapter]

def elastic (i:Veil c f):Head S:= Sum.inr (.inr (.inl (chapter i)))
lemma runOut:Injective (elastic (S:=S)) := ((Sum.inr_injective).comp ((Sum.inr_injective).comp (Sum.inl_injective.comp Fan.padded)))
def coming (χ: ChartRatio G)(R:Rep G f) (X:Coat T F)(p:Disk G c) (z:Air f G) : Veil c f→ℝ:=
    let a:= -R.beta*Raw.orientation
    Sum.elim (fun i=> -R.activities.E i (inputΛ X z p)) (Sum.elim (fun i=>atomΛ X R.path.cubic i a z p) (Sum.elim
      (fun i=>atomΛ X R.path.quartic i a z p) (Sum.elim (fun i=>atomΛ X R.path.loop i (-Raw.orientation) z p) (Sum.elim (fun i=> a*sourceΛ X i z p) (Sum.elim (timeΛ X p).undercurrent (fun i=> solar X z χ p i))))))
def postponement (L:Side)(t:ℝ)(o:Target.Order G W):=o.ξ*(Delay.fineMonitor G L t/2)
def vows (X:Coat T F) (R:Rep G f) (Q: YM.ConnectedActivityE6.Target G P) (a:ℝ) (x: Disk G c) (z:Air f G)(i:Veil c f):=
    let Z:= timeΛ X x
    let u:= worldZ Z R.beta z
    Polar.logMoment Z a R Q.table u (Z.input u) z (chapter i)
lemma longing (X:Coat T F) (H: Cash W s η L Q o t T R)(hX:X.x=s)(hm:X.width=o.K) (hT:Stamp T)(x: Directions G c)(p:= (gStep R.beta,x)) (hP:p=(gStep R.beta,x))(hp:(timeΛ X p).manifest) (z: Air f G)(he:∀ i,|z i|≤ postponement L s o):
    coming Q.table R X p z=fun i=> vows X R Q o.a p z i:=by
  have hθ:=H.laws.data; have hx:=H.laws.intake
  obtain ⟨h₀,h₁,h₂,h₃⟩:=hθ.safety
  let Z:=timeΛ X p
  let U:=worldZ Z R.beta z; have he' : Z.liftA R.beta z=U:= Vine.shine Z (show Room P S T Z.x from hX.symm ▸ H.laws.data.room
    ) hp R.beta z
  have hV (v:Site c): Z.watch v o.ξ R.beta Z.B z:= fun i hi=> le_trans (he i) (by
    apply le_trans (b:=o.ξ*(Z.t*(gStep R.beta)⁻¹)) (mul_le_mul_of_nonneg_left _ o.rare.le) (le_of_eq (by ring))
    unfold Coat.t; rw [show Z.x=s from hX, ← hθ.funds.length_eq]; exact (charge_area S s T R hx))
  have hi : Intake P T Z.x R := hX.symm ▸ hx -- check
  have hz:= h₃ F Z hX hm hp; have hf:0 < Z.t:= R.p.threshold_pos.trans_eq hi.received.temp
  have hA:0<o.a*Z.t:=mul_pos o.large hf
  have HH (i: Bond f): Z.cone (2*o.a) U i=1:= Z.serves hA _ _ (by
     rw [Z.premiere hA U i]; swap
     · have hP := Z.watch_bonds (atEdge S i) hf o.rare.le hx.positive (hV (atEdge S i)) i (by rw [separation_self]; omega) (hz.1 i)
       rw [← he']; exact hP.2.trans (mul_le_mul_of_nonneg_right (by linarith) hf.le)
     norm_num)
  have hs : switchΛ X z p=U:= by change _=worldZ (timeΛ X p) _ _; rw [hP,rims]
  have hU: Z.input U=inputΛ X z p:= by rw [openingΛ, hs]
  have hF (i:Bond f)(W : Finset (Bond f)): Z.enforce (2*o.a) U W=1:= Finset.prod_eq_one fun i _=> HH _
  have hj: RG.flags R.p.threshold (inputΛ X z p) = ∅:= by
    apply Finset.not_nonempty_iff_eq_empty.mp; rintro ⟨y,hy⟩
    obtain ⟨k,-,hk⟩:= (flags_spec ..).mp hy; let i:= S.ratio.parent k.1
    have he : ¬ Inside i Z.seeds (30*Z.B) := X.blank_no i _
    have hp : toll (Z.input (Z.liftA _ z)) k < Z.t/4 := (hz.2 hT i he R.beta hx.positive z (hV i)).2.1 k rfl
    rw [he',hU] at hp; rw [hi.received.temp] at hk; change Z.t < toll _ k at hk; linarith only [hf,hp,hk]
  have ht (s:Signed): RG.flags R.p.threshold (pull s 0 (inputΛ X z p))=∅ := by
      exact PhysicalNext.Repeat.Pane.tranquility _ hj _ _
  have hb {d:ℕ}(A:ℕ→Atom G d)(i:Trans f)(r:ℝ):translateValue R.p A r (Z.input U) i=atomΛ X A i r z p :=by
    unfold translateValue Atom.placed atomΛ; rw [hU,RG.masked_eq _ _ _ _]; unfold Healthy; simp only [ht]; simp
  ext i; unfold coming vows chapter; rcases i with i|i|i|i|i
  · dsimp only [Sum.elim]; change -_ = -(R.activities.regularOccurrence _ i (Z.input U))* Z.enforce ..; rw [hF (0,0),mul_one,Activities.regularOccurrence,hU,RG.masked_eq _ _ _ _]; unfold Healthy; rw [hj]; simp
  · change atomΛ .. = translateValue .. * Z.enforce ..; rw [hF (0,0),mul_one,hb, show -R.beta*orientation=-orientation*R.beta by ring]
  · change atomΛ .. = translateValue .. * Z.enforce ..; rw [hF (0,0),mul_one,hb, show -R.beta*orientation=-orientation*R.beta by ring]
  · change atomΛ .. = translateValue .. * Z.enforce ..; rw [hF (0,0),mul_one,hb]
  rcases i with i|i|i
  · change (-R.beta*Raw.orientation)*sourceΛ X i z p=if Inside _ Z.seeds _ then 0 else _ *(_ * _ + _); rw [if_neg (show ¬Inside (rowSite S i) Z.seeds (200*Z.B) from X.blank_no _ _)]; unfold sourceΛ
    rw [hF (0,0),one_mul]; apply congrArg ((-R.beta*Raw.orientation)* ·); refine congr_arg₂ (·+·) ?_ rfl
    have hv:= Vine.patch_rep X (pass p) U i
    dsimp only at hv; unfold orbitΛ twig; rw [hs]; exact hv.symm
  · rfl
  change solar X z Q.table p i=Z.solo U Q.table o.a i; unfold solar solo; split
  next h=> rw [if_pos (show i∉Z.plaza (Z.seeds.dome (304*Z.B)) ∧ Z.Hot i from h),gentry,HH,one_mul,hs]
  next h=> exact (if_neg h).symm
end YM.LocalLTE.Fan
