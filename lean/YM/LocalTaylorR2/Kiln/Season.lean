import YM.LocalTaylorR2.Kiln.Power
import YM.LocalTaylorR2.Kiln.Enfold

/-! # Price all REST principal/path together -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Kiln
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Work.G05
variable {G:Gauge}{c f L n : Side} {S:StepData c f}{P:Teller G}{T:Tube G S}{F:Forest S.ratio}
variable {d j k p:ℕ}{s:ℝ}{R:Rep G f}
variable {X X': Coat T F} {A : ℕ→ Atom G d}{i:Trans f}
open Itinerary Mesh Port Pavilion
variable {W C μ:ℝ}{Q:YM.ConnectedActivityE6.Target G P}{o:Target.Order G W}

def cub (H:Cash W s μ L Q o C T R) (p:ℕ) (i:LogIndex c f):Port.Test T:= match i with
| .inl (.inr (.inl i)) => Kiln.flame H (-Raw.orientation*R.beta) R.path.cubic i (p+3)
| .inl (.inr (.inr (.inl i))) => Kiln.flame H (-Raw.orientation*R.beta) R.path.quartic i (p+3)
| .inl (.inr (.inr (.inr (.inl i)))) => Kiln.flame H (-Raw.orientation) R.path.loop i (p+3)
| _ => mosaics H p i

set_option maxHeartbeats 400000 in
lemma cub_more (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(D:Patch)(hD:D.Branches P.bind G)(b a ζ :ℝ)(d v:ℝ→ℝ)(hv:Rate G L (-(1/2)) v)(he:∀ᶠ x in atTop,0≤v x)(hd:Rate G L (-(1/2)) d)(hz:-(1/2:ℝ)<b)(hb:a≤1/2)(χ:Chi)(o:Target.Order G W)(p j:ℕ)(μ:ℝ): ∀ᶠ x in atTop, ∀(c f:Side) (S:StepData c f)(T:Tube G S)(R:Rep G f)(C:ℝ)(H:Cash W x μ L Q o C T R), S.patch=D → ∀ r y :ℝ, ∀ w, let γ:= betaF G x L^a; 1≤r → Meter (H:=H) (mosaics H p) p ζ r (v x) (d x) γ y j χ w → ∃ z, Meter (H:=H) (cub H p) p ζ r (v x) (d x) γ (y+3*(betaF G x L)^b) j χ z:=by
  let x n:=portrait G P o L (primary G) D hD v d hv hd he n j (p+3) χ Q.halo
  choose! W₀ W' hW hrW h using x
  have h₀ n:Rate G L (-((p+4:ℕ):ℝ)/2) (W₀ n):= hW n
  have hP :0≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  have hc:= Q.grants.2.1
  filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1,h 3,h 4,h 2,
    shops G L Q.halo p 3 P.top.width _ _ Q.usable hP hc (h₀ 3) (hrW 3) (Rate.const P.top.paths) a 0 b hb (by norm_num) hz,
    shops G L Q.halo p 4 P.top.width _ _ Q.usable hP hc (h₀ 4) (hrW 4) (Rate.const P.top.paths) a (1/2) b hb (by rfl) hz,
    shops G L Q.halo p 2 P.top.width _ _ Q.usable hP hc (h₀ 2) (hrW 2) (loopBill_rate G L) a (1/2) b hb (by rfl) hz]
    with X hX h₃ h₄ h₂ H₃ H₄ H₂ c f S T R C H hp r y w γ hr hY
  have hx:= H.laws.intake; have hZ:= H.laws.data; have hh:= hZ.funds.length_eq; have hz := hx.window.2; have hR:= hx.cap.paths; rw [hh] at hR hz
  let l:= -(Raw.orientation); let ℓ:= l * R.beta
  let Φ:= betaF G X L; have hg: |l|≤1:= by rw [show |l|=Raw.orientation by unfold l; rw [abs_neg,abs_of_nonneg Raw.orientation_range.1.le]]; exact Raw.orientation_range.2
  have hb: |ℓ|≤2*betaF G X L:=by
    unfold ℓ; rw [abs_mul,abs_of_nonneg hx.positive.le]; apply le_trans (mul_le_mul_of_nonneg_right hg hx.positive.le) ?_; rw [one_mul]; exact hz
  have hS3:= H₃ c f S hh R.path.cubic hR.three ℓ hb; have hS4:= H₄ c f S hh R.path.quartic hR.four ℓ hb
  have hS2:= H₂ c f S hh R.path.loop hR.two l (by linarith)
  let g : ∀{d}, (ℕ→Atom G d)→ Trans f→ℝ→ℝ:=fun {d} A i η=> bill (W₀ d X) (W' d X) η X A i * γ^p; let z: LogIndex c f→ℝ:= Sum.elim ( Sum.elim (fun _=>0) (Sum.elim (fun i=>g R.path.cubic i ℓ) (Sum.elim (fun i=>g R.path.quartic i ℓ) (Sum.elim (fun i=>g R.path.loop i l) fun _=> 0)))) fun _=> 0
  have hr:0<γ:= Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) a
  let M:=(Φ:ℝ)^b
  have hV : Sales (radiusB X) Q.relative Q.ε (roadway T R (radiusB X) Q.halo) (fun i=> Φ^leaseLog ζ c f i*z i) (exCharge T R) (3*M):=by
    rw [show 3*M =0+(M+(M+(M+0)))+0 from by ring]; have h:=( (Mesh.free (regularFoot S.ratio Q.halo (radiusB X) R) (regularExtra R) (radiusB X) Q.relative Q.ε).together (hS3.together (hS4.together (hS2.together (Mesh.free (Sum.elim (bothFoot S.ratio Q.halo (radiusB X) R.path) (bothFoot (atOne c) Q.halo (radiusB X) T.down)) (Sum.elim (bothCharge R.path) (bothCharge T.down)) (radiusB X) Q.relative Q.ε))))).together (Mesh.free (Sum.elim (sleeve S (radiusB X) Q.halo) (basisFoot S (radiusB X) Q.halo)) (Sum.elim (fun _=>0) (basisCharge f)) (radiusB X) Q.relative Q.ε)
    convert h using 1
    · rfl
    · funext i; rcases i with (i|(i|(i|(i|(i|i)))))|i|i <;> try exact rfl
      all_goals exact mul_zero _
    rfl
  have hw j : 0≤ w j:= nonneg_of_mul_nonneg_right (hY.hashes.nonneg _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) _); have hv j:0≤z j:= nonneg_of_mul_nonneg_right (hV.nonneg _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) _)
  refine ⟨w+z,?_, ?_, ?_⟩
  · intro i; rcases i with (i|(i|(i|(i|(i|i)))))|i|i
    · exact hY.keptP _
    · exact snuffed _ R.path.cubic _ i _ D hD hp (hR.invariant _).2.1 (logTest H (Sum.inl (.inr (.inl i))))
    · exact snuffed _ R.path.quartic _ i _ D hD hp (hR.invariant _).2.2 (logTest H (Sum.inl (.inr (.inr (.inl i)))))
    · exact snuffed _ R.path.loop _ i _ D hD hp (hR.invariant _).1 (logTest H (Sum.inl (.inr (.inr (.inr (.inl i))))))
    all_goals exact hY.keptP _
  · convert nab hY.hashes hV using 1; ext i; unfold Φ; simp only [Pi.add_apply,mul_add]
  intro i
  have ht i:= (hY.tick i).climb H (mul_le_mul_of_nonneg_right (show w i ≤ (w+z) i from le_add_of_nonneg_right (hv _)) (inv_nonneg.mpr (pow_nonneg hr.le _))) le_rfl
  have hx k (i:Trans f)(A: ℕ→Atom G k) η i' (ht : Sees H j (v X) (d X) χ (error (cub H p) H i') (bill (W₀ k X) (W' k X) η X A i) (seating Q.halo X S A i)) (hz:z i'=g A i η) (hc:spanW T R (radiusB X) Q.halo (identityLog (S:=S) i') = seating Q.halo X S A i): Sees H j (v X) (d X) χ (error (cub H p) H i') ((w+z) i'*(γ^p)⁻¹) (r* spanW T R (radiusB X) Q.halo (identityLog (S:=S) i')):=by
    apply ht.climb H; swap; · rw [hc]; exact le_mul_of_one_le_left (zero_le_one.trans (sit_ge ..)) ‹1≤r›
    apply le_trans _ (mul_le_mul_of_nonneg_right (show z i' ≤ (w+z) i' from le_add_of_nonneg_left (hw _)) (inv_nonneg.mpr (pow_nonneg hr.le _)))
    apply le_of_eq; rw [hz]; unfold g; field
  rcases i with (i|(i|(i|(i|(i|i)))))|i|i
  · exact ht _
  · exact hx _ i R.path.cubic ℓ _ (h₃ _ _ S T R Q μ C H hp ℓ _ i (hR.invariant _).2.1) rfl rfl
  · exact hx _ i R.path.quartic ℓ _ (h₄ _ _ S T R Q μ C H hp ℓ _ i (hR.invariant _).2.2) rfl rfl
  · exact hx _ i R.path.loop l _ (h₂ _ _ S T R Q μ C H hp l _ i (hR.invariant _).1) rfl rfl
  all_goals exact ht _

def resting (G:Gauge):Regime G where
  symbol H p:= cub H p
  enroll P Q:=by
    obtain ⟨k,h⟩:= (stars G).enroll P Q; refine ⟨k,fun L he D hD i l χ W hw μ hp o v d hv hT hd a b ζ ha hμ hz=>?_⟩
    obtain ⟨f,hB,hF⟩:= h L he D hD i l χ W hw μ hp o v d hv hT hd a b ζ ha hμ hz; refine ⟨fun x=>f x+3*(betaF G x L)^b,hB.add (Rate.power.mul_left 3),?_⟩
    filter_upwards [hF,cub_more P Q L D hD b a ζ d v hv hT hd hμ ha χ o l i μ] with x h g c f S T R C H ht hw r hr; obtain ⟨w,hw⟩:= h _ _ S T R C H ht hw _ hr; exact g _ _ S T R C H ht _ _ w hr hw
end YM.LocalTaylorR2.Kiln
