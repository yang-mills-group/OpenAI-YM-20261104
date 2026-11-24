import YM.LocalTaylorR2.Mesh.Pigment
import YM.LocalTaylorR2.Dispatch
/-!
 # Afford even after replacing whole symbols by finite-degree analytic kernels.
 Not dependent on a metric shear/new density. Support and affordability checked.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Mesh
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Port Channel Next.Foundations Itinerary Reserves
variable {Ñ:ChartRatio G} {i p:ℕ} {v d A a y r B g D C' θ α M ζ ρ:ℝ}

structure Meter {H:Cash W s μ L Q o C T R}(g : LogIndex c f→ Port.Test T)(p:ℕ)(ζ θ v d ρ D : ℝ)(i:ℕ)(χ:Chi)(w:LogIndex c f→ℝ):Prop where
  keptP (q:LogIndex c f) : Kept H (H.supportP (identityLog q)) (g q)
  hashes : Sales (radiusB s) Q.relative Q.ε (roadway T R (radiusB s) Q.halo) (fun i=> betaF G s L^leaseLog ζ c f i* w i) (exCharge T R) D
  tick : ∀ q, Sees H i v d χ (error g H q) (w q*(ρ^p)⁻¹) (θ*spanW T R (radiusB s) Q.halo (identityLog (S:=S) q))

lemma nab {ι:Type*} {w:ι→ℝ} {f:ι→Support c} {g:ι→ℕ} {v:ι→ℝ}{b l t t':ℝ}(h:Sales i b l f w g t)(h':Sales i b l f v g t'):Sales i b l f (w+v) g (t+t'):=by
  refine ⟨fun i=>add_nonneg (h.nonneg i) (h'.nonneg i),fun x=>?_⟩; convert budget_plus (h.hit x) (h'.hit x) using 1; funext j; dsimp only [tariff,Pi.add_apply]; split
  · simp only [add_mul]
  simp
lemma free {ι:Type*} (H:ι→Support c)(p:ι→ℕ) (k:ℕ)(b l:ℝ): Sales k b l H (fun _=>0) p 0 := ⟨fun _=>le_rfl,fun x=>by apply budget_of_sum <;> simp [tariff]⟩
variable {χ:Chi}
lemma increasing (Ξ:Utopia H i v d r C' χ)(hI:LocalBookingsR2 ζ B Ξ) (L':LogIndex c f→ Port.Test T)
    (h:1≤betaF G s L)(hζ:0≤ζ){w:LogIndex c f→ℝ} (he : Meter (H:=H) L' p ζ r v d ρ D i χ w) (hi:B+D≤ Q.goal L s):
    ∃ U:Utopia H i v d r C' χ, U.goalsL=Ξ.goalsL+w ∧ LocalBookingsR2 ζ (B+D) U:=by
  have ht := he.hashes
  have hh q : 0≤ w q:= nonneg_of_mul_nonneg_right (ht.nonneg _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le h) _)
  set w':= Ξ.goalsL+w
  let s':= radiusB s
  have hy: Sales s' Q.relative Q.ε (footprints T R Q.halo s') (fun i=>betaF G s L^lease ζ c f i*rates Ξ.goalsK w' (Ξ.M*Ξ.rad) i) (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (B+D):=by
    have hv:= (free (forcedFoot S.ratio Q.halo s' R) (forcedExtra R) s' Q.relative Q.ε).together (ht.together (free (field_support S s' Q.halo) (fun _ : WarningAt c f=>0) s' Q.relative Q.ε))
    -- specify support basis def WarningFoot
    let ht':= nab hI.leases hv; rw [zero_add,add_zero] at ht'
    convert ht' using 1
    funext j; rcases j with j|j|j <;> simp only [lease, rates,Pi.add_apply,Sum.elim, Utopia.flair, add_zero]
    unfold w'; simp only [Pi.add_apply,mul_add]
  let U: Utopia H i v d r C' χ:={ Ξ with
    goalsL:= w'
    uses:= (loosen (leaseNN hζ) h hy).raise hi
    stream:=by
     intro E _ _ _ F X Y u z x Z ht hw hχ hm hp he H' k j hv
     apply (Ξ.stream E F X Y u z x Z ht hw hχ hm hp he k j hv).climb ?_ le_rfl
     rcases j with j|j|j|j <;> first | exact le_rfl | exact le_add_of_nonneg_right (hh j) }
  exact ⟨U,rfl,hy,fun E _ _ _ F X V u z x Z ht hw hχ hm hp he i=> (hI.logsT E F X V u z x Z ht hw hχ hm hp he i).climb (le_add_of_nonneg_right (hh i)) le_rfl⟩

lemma tempo (G:Gauge)(P:Teller G) (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(D v E:ℝ→ℝ)
    (hV : Rate G L (-(1/2)) D)(hE : Rate G L α E)(hL:α ≤ 1/2)(o:Target.Order G W) (ζ:ℝ)(p i:ℕ)(χ:Chi):
    ∃ Y : ℝ→ℝ, Rate G L (-(1/2)) Y ∧ ∀ᶠ x in atTop, 0 < E x → ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(μ C:ℝ)(R:Rep G f)(H:Cash W x μ L Q o C T R) r, 1≤r → ∃ w, Meter (H:=H) (part H p) p ζ r (v x) (D x) (E x) (Y x) i χ w:=by
  obtain ⟨U,hU,hN,hp⟩:= errorLaw Q.table Q.table_exists o.a D hV p i χ
  let A x:= (E x)^p*U x
  have hA : Rate G L (-(1/2)) A:=by
    convert! (((hE.weaken hL).pow p).mul hU) using 1; ring
  let m:= Fintype.card Signed*Census.spots L+(Itinerary.density L+ Itinerary.density L)
  let b x:= ((Animals.ballCost ((Q.halo+1)*radiusB x):ℝ)*m)*(A x*Real.exp (Q.relative*Animals.ballCost (Q.halo+1)))
  have hv:=Census.width_rate G L (Q.halo+1) 0; simp only [add_zero] at hv
  refine ⟨b,by simpa only [zero_add] using! (hv.mul_right m).mul (hA.mul_right _),?_⟩
  filter_upwards [hp] with x hp hX c f S T μ C R H r h
  have hx:= H.laws.data.funds.length_eq; have hy:= H.laws.data.room
  have he:0≤A x:=mul_nonneg (pow_nonneg hX.le _) (hN _)
  have hl := YM.ConnectedActivityE6.fixed (ε:=Q.ε) (C:=A x) (smallCensus S L hx) (show 0<radiusB x from lt_of_lt_of_le (by norm_num) hy.sight.1) _ (packed S (l:=Q.halo) (lt_of_lt_of_le (by norm_num) hy.sight.1)) (show 0≤Q.relative by unfold Target.relative;linarith [Q.usable,Q.bound,Q.pos]) he
  let d:=Sum.elim (fun _ : LogLetter c f=> (0:ℝ)) (Sum.elim (fun _ :Miniature c f=> A x) (fun _ : ChainIndex f=> (0:ℝ)))
  refine ⟨d,control H,?_,fun j=>?_⟩
  · have hz:= (free (Raw.space T Q.halo (radiusB x) R) (Raw.extra T R) (radiusB x) Q.relative Q.ε).together (hl.together (free (basisFoot S (radiusB x) Q.halo) (basisCharge f) (radiusB x) Q.relative Q.ε)); rw [zero_add,add_zero] at hz
    convert hz using 1; · rfl
    · funext j; rcases j with j|j|j <;> simp only [leaseLog,d,Sum.elim,mul_zero,Real.rpow_zero, one_mul]
    rfl
  have hb : 1 ≤ r * spanW T R (radiusB x) Q.halo (identityLog (S:=S) j):= one_le_mul_of_one_le_of_one_le h (le_add_of_nonneg_right (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  rcases j with j|j|j
  · intro G _ _ _ F X Y u z y Z _ _ _ _ _ _; simp_rw [error,part,sub_self]; exact (certified (zero_le_one.trans hb) (0:ℝ)).climb (by simp [d]) le_rfl
  · apply (hp c f S T W μ C P Q o R H rfl rfl _ j).climb H _ hb; apply le_of_eq; simp [d,A,hX.ne',mul_comm (E x^p)]
  intro G _ _ _ F X Y u z y Z _ _ _ _ _ _; simp_rw [error,part,sub_self]; exact (certified (zero_le_one.trans hb) (0:ℝ)).climb (by simp [d]) le_rfl
end YM.LocalTaylorR2.Mesh
