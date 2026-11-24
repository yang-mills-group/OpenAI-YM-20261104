import YM.LocalTaylorR2.Test

/-!
# Keep the test through a field-dependent Gaussian recoil

E6 Tropolis proof, generalized to `Kept`; preserve both location checks
and the Jacobian `scalp`. The resulting integration formula uses all
probability laws of E6, not a new measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Port
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Bloch Laurent Channel Next.Foundations
variable (I : Finset (Bond f)) (X : Coat T F)
variable {Y : Support c} {K : Test T} {a d A:ℝ}
variable (V : Config G c) (h : Canary G d A) (hV : Drivable X d A V) (hx : X.x=s) (hk : X.width=o.K) (hK : Kept H Y K)

def tilted (β : ℝ) (I : Finset (Bond f)) (X : Coat T F) (V : Config G c) (d : ℝ) (K : Test T) (z : Air f G) : ℝ :=
  scalp I X V β d z * K F (vary X V) (course X d β z V)
def duoTilt (β : ℝ) (I : Finset (Bond f)) (X : Coat T F) (V : Config G c) (d : ℝ) (K : Test T) (z : F.Slice G×Air f G) : ℝ :=
  tilted β I (X.wrapY z.1) V d K z.2
def average (X : Coat T F) (I : Finset (Tubular f G)) (K : Test T) :=
  ∫ Y, (∫ z, lens₀ (Pond.circuit I X.relating) z * K F (X.wrapY Y) (Pond.spill I z)) ∂ F.order G

include h hV hx hk hK
lemma measurableTilt {E : Type} [MeasurableSpace E] {Z:E→ F.Slice G} {z:E→ Air f G}
    (he:Measurable Z) (hp:Measurable z) : Measurable (fun i=> tilted R.beta I (X.wrapY (Z i)) V d K (z i)) := by
  have ht : Intake P T X.x R:= hx.symm ▸ H.laws.intake
  have hΞ : ShellAccess S G X.x W X.width o.γ:= by rw [hx,hk]; exact H.laws.data.access
  let P' i:=X.wrapY (Z i); let f x:=course (P' x) d R.beta (z x) V
  obtain ⟨hJ,hZ⟩:= Flux.steering I X h V hV he hp ht.ready hΞ R.beta
  have hm (B : Coat T F) {_V : E→ Body (↥ (lensS I G))} (he:Measurable _V):=bulbB (fun _ _=> measurable_const : Borel fun i:E=> circuit (lensS I G) B.relating) he
  have hF : Measurable (fun x=> scalp I (P' x) V R.beta d (z x)) := hJ.mul ((show Measurable fun x=> lens₀ (circuit (lensS I G) (vary X V).relating)
    (Pond.swim _ (f x)) from hm (vary X V) ((swim_m (lensS I G)).comp (show Measurable f from hZ))).div (hm X ((swim_m (lensS I G)).comp hp)))
  exact hF.mul (hK.borel E F X hx hk (fun _ => V) Z f measurable_const he hZ)

lemma recoilLaw (hp : X.relating.PosDef) (hv : I=edgesM S Y X.B) :
    average (vary X V) (lensS I G) K=∫ x, (∫ z,tilted R.beta I (X.wrapY x) V d K z ∂X.dice) ∂ F.order G := by
  unfold average; apply integral_congr_ae; filter_upwards with x
  have ht : Intake P T X.x R:= hx.symm ▸ H.laws.intake
  let B:= lensS I G; let Z:= X.wrapY x; let A':= circuit B X.relating
  let J:= sweep A'; have hP : MeasurePreserving (swim B) X.dice J := Pond.orbit hp.posSemidef B
  let f : Air f G → ℝ:= tilted R.beta I Z V d K
  have hF : Measurable f := measurableTilt I X V h hV hx hk hK (Z:=fun _=>x) (z:=id) measurable_const measurable_id
  have hB : B=podium S G Y X.B := by unfold B; rw [hv]; exact chargedU ..
  have hf : confined (swim B) f := by
    intro u v hh; unfold f tilted; rw [Flux.slab I Z V u v hh d]; apply congrArg
    have hp := congr_arg (pitch I Z d R.beta V) hh; rw [pitch_alt,pitch_alt] at hp
    exact hK.links F _ _ _ _ hx hk Y (Subset.refl _) (Village.refl ..) (show Pond.swim (podium S G Y X.B) _=Pond.swim (podium S G Y X.B) _ from hB ▸ hp)
  have he: Drivable Z d A V := ⟨fun i=> hV.good i⟩
  let F' z:=lens₀ (circuit B (vary Z V).relating) z * K F (vary Z V) (Pond.spill B z)
  change (∫ z,F' z) = ∫ z,f z ∂X.dice
  rw [Pond.gathered (Pond.spill B) (spill_m B) hP (settled _) hf hF]
  change _ = ∫ z, f (Pond.spill B z) ∂ sweep A'
  rw [gyre I Z h ht.positive V he F', Shield.recommends A' (show A'.PosDef from hp.submatrix Subtype.val_injective) _]
  apply integral_congr_ae; filter_upwards with y
  let z:= spill B y; let w:= course Z d R.beta z V; let b:=pitch I Z d R.beta V y; let E v:= K F (vary Z V) v
  have hG : E (Pond.spill B b)=E w := by
    apply hK.links _ _ _ _ _ (show (vary Z V).x=s from hx) hk Y (Subset.refl _) (Village.refl ..)
    change swim (podium S G Y X.B) _=swim (podium S G Y X.B) _
    -- avoid dependency on b: from equal Air coordination
    let u:=Pond.spill B b; have hf : ∀ i ∈ B, u i=w i := (observe B).1 (settled B b)
    exact (observe _).2 (fun i hi=> hf i (hB.symm ▸ hi))
  change jacL _ Z d R.beta V z*(lens₀ _ b*E _)=lens₀ A' y*(scalp I Z V R.beta d z* E w)
  have hp : scalp I Z V R.beta d z=jacL I Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b/lens₀ A' y) := by
    unfold scalp; dsimp only; rw [show swim B z=y from settled ..]; rfl
  change jacL _ Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b*E _)=_
  rw [hG,hp]; field_simp [ne_of_gt (fullFuel A' y)]
end YM.LocalTaylorR2.Port
