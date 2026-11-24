import YM.MSbar.Cottage.Copy
import YM.MSbar.LocalSD.Expect
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {U V U' V' :Config G f}{R: Rep G f}{σ C T a v δ w β:ℝ}
open Finset RG.PathData Tree
variable {Y X: Support f}
open AnalyticBridge.VerifiedReset Next.Scheduling Precision
variable (F: Forest S.ratio)(X:Finset F.Free)(G' : Gauge)
abbrev IV (P : Gauge) := (↑X → P.El)
def fence := Measure.pi (fun i:↥ X=> G'.probHaar)
instance vine : IsProbabilityMeasure (fence F X G'):=by unfold fence; infer_instance
lemma climber (J:IV F X G'): MeasurePreserving (· * J) (fence F X G') (fence F X G') :=measurePreserving_pi (fun _=> G'.probHaar) (fun _=> G'.probHaar) fun i=>measurePreserving_mul_right G'.probHaar (J i)
lemma climbing : MeasurePreserving (Inv.inv : IV F X G'→ IV F X G') (fence F X G') (fence F X G') := measurePreserving_pi (fun _=> G'.probHaar) (fun _=> G'.probHaar) fun _=> G'.preserve_inv
variable {G'} (τ: IV F X G)
def pegged : F.Slice G :=fun i=> if h:i∈X then τ ⟨i,h⟩ else 1
local notation "Λ"=> IV F X G
local notation "ι!"=> fence F X G
local notation "U!"=> Config G f
local notation "N" => prior G f
def twirl:= pedal (G:=G) F (pegged F X τ)
local notation "β!"=> twirl F X
lemma ends (x y:Λ) (U:U!) : β! x (β! y U)=β! (x*y) U:=by
    funext i; change (F.foldAt (β! y U) i.1)⁻¹ * F.drape (pegged F X x) i * F.foldAt (β! y U) i.1 * (β! y U i)= _; rw [show F.foldAt (β! y U) i.1=F.foldAt U i.1 from congr_fun (centered F (pegged F X y) U) i.1]
    have h : F.drape (pegged F X (x*y)) i= F.drape (pegged F X x) i* F.drape (pegged F X y) i:=by
       by_cases hi: i∈ F.trunks; simp only [show ∀ W:F.Slice G,F.drape W i=1 from fun W=>F.on_tree W ⟨i,hi⟩,one_mul]
       let u:F.Free:=⟨i,hi⟩
       all_goals simp only [show ∀ W:F.Slice G,F.drape W i=W u from fun W=>F.off_tree W u,pegged]; split <;> first|rfl|exact (one_mul _).symm
    unfold twirl pedal; rw [h]; group
lemma stay : β! (1:Λ) U=U:=by
    funext i; unfold twirl pedal; have he :F.drape (pegged F X (1:Λ)) i=1:=by
       by_cases hi:i∈ F.trunks; exact F.on_tree _ ⟨i,hi⟩
       let u:F.Free:= ⟨i,hi⟩; exact (F.off_tree _ u).trans (by unfold pegged; split <;> rfl)
    rw [he]; group
lemma twirlD (G:Gauge) : Continuous (fun p:IV F X G × Config G f=> β! p.1 p.2) := by
    refine continuous_pi fun j=>?_ ; unfold twirl pedal; apply Continuous.mul; apply Continuous.mul; apply Continuous.mul; fun_prop
    · by_cases hj:j∈ F.trunks
      · simp_rw [show ∀ W:F.Slice G, F.drape W j=1 from fun W=>F.on_tree W ⟨_,hj⟩]; exact continuous_const
      let i:F.Free:=⟨j,hj⟩; simp_rw [show ∀ W:F.Slice G,F.drape W j=W i from fun W=>F.off_tree W i,pegged]; by_cases hi:i∈X; simp only [dif_pos hi]; fun_prop
      simp only [dif_neg hi]; exact continuous_const
    all_goals fun_prop
lemma backdrop {α γ :Type*}[MeasurableSpace α][MeasurableSpace γ]{f : α→ℝ}(h:Envelope f){v:γ→α}(hp: Measurable v): Envelope (f∘v):=by obtain ⟨p,hH⟩:=h.cost; exact ⟨h.meas.comp hp,p,fun i=> hH _⟩
lemma unroll {α γ:Type*}[MeasurableSpace α] [MeasurableSpace γ] {μ:Measure γ} [IsProbabilityMeasure μ]{f:α× γ→ℝ}(h:Envelope f): Envelope (fun i:α=> ∫ y, f (i,y)∂ μ):=by
    refine ⟨h.meas.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩; obtain ⟨b,hb⟩:=h.cost; refine ⟨b,fun i=>?_⟩
    let f'(y:γ):= f (i,y); have hv:Envelope f':= backdrop h (show Measurable (fun y:γ=>(i,y)) from measurable_const.prodMk measurable_id)
    apply (norm_integral_le_integral_norm ..).trans; refine (integral_mono (hv.integrable μ|>.norm) (integrable_const b) (fun i=> hb _)).trans_eq ?_; simp
-- group average Tonelli weighted.Before Insert
lemma voyage (g:Λ× U!→ℝ) (h:Envelope g) (he:∀ i:Λ,S.Inner (fun U:Config G f=> g (i,U))) :
     (∫ t,∫ U, g (t⁻¹,β! t U)∂ N ∂ι!)=∫ t,∫ U, g (t,U)∂ N ∂ι!:= by
    have hF(i:Λ) : Envelope (fun U:Config G f=> g (i,U)):= backdrop h (show Measurable fun U:Config G f=> (i,U) from measurable_const.prodMk measurable_id)
    calc _ = (∫ t:Λ,∫ U,g (t⁻¹,U)∂ N∂ι!):=integral_congr_ae (Eventually.of_forall (fun t=> tribute F (pegged F X t) (fun U:Config G f=>g (t⁻¹,U)) (he t⁻¹) (hF t⁻¹)))
         _ = _ := (climbing F X G).integral_comp (Homeomorph.inv (G:=Λ)).measurableEmbedding (fun t=>∫ U,g (t,U)∂ N)
local notation "XX"=> twirl F X
end YM.MSbar.Heath.Cottage
