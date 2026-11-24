import YM.Contacts.Junction.Lemon
/-! # canonical weighted exp lights. Fact.Cubits arith. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω' s a:ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums SectorMeasure Presented Next.Fluctuations Next.Fluctuations.Sector
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
namespace StagePort
variable (p:StagePort G U P X k L σ C M n)
local notation "D" => (p.dew)
local notation "J" => (p.dew.label)
local notation "g" => (p.dew.grad)
local notation "β" => (p.dew.β)
local notation "χ" => (p.dew.matrix)
def shiftV (x:(D).X)(z:(D).Y):= (D).L x+g • z
abbrev stainP (x:(D).X)(z:(D).Y):= draw (D).B (Cove.ship x) (p.shiftV x z)
abbrev utterance (x:(D).X)(z:(D).Y) := flags p.budget.threshold ((D).B.drape (p.stainP x z))=∅
abbrev outerP := Sector.prefactor (D).S G β
abbrev worker := P.scale^Fintype.card (D).B.Free * p.outerP
abbrev sizes :ℕ:= Fintype.card (Precision.Key (D).B G)
def grader := worker p * Junction.law χ * g^(p.sizes)
def dream (x:(D).X):= grader p *Real.exp (-β*((D).℘ x))
-- cannon uses ℓ of bench and explicit β not g^-2.Concept. seam Green all radius.
abbrev hint (x:(D).X)(z:(D).Y):= β* (p.bench- p.natal) (p.crab x z)
abbrev warmth (x:(D).X)(z:(D).Y):= Real.exp ( -(g⁻¹ ^2)* (p.bench-skel p.bench 3) (p.crab x z))
abbrev warm (x:(D).X)(z:(D).Y):ℝ:= p.warmth x z * Real.exp (p.hint x z)
def shadeV (x:(D).X)(z:(D).Y): ℝ:= if p.utterance (p.flag • x) z then p.warm x z else 0
local notation "p₀" => Real.exp
variable {p}
lemma variation {z:p.dew.Y}(x:ℝ): Junction.gram p.dew.B χ (x • z)=x^2*Junction.gram p.dew.B χ z:= by unfold Junction.gram; erw [WithLp.ofLp_smul,Matrix.mulVec_smul, smul_dotProduct,dotProduct_smul]; rw [smul_eq_mul,smul_eq_mul]; ring
variable (hp:Pearl U p.taxi p.pearlRide L σ C M n p.budget p.dew)(hP:LocalRatio P)
include hp hP
lemma matter (x:(D).X):0<p.dream x:= by
    have h:= hp.intake.positive; have hx:0<g:=(gS β h).1; have ht:0<Junction.law χ := inv_pos.mpr (Shield.fullFuel ..); have he:0< p.outerP:= Sector.prefactor_pos β; unfold dream grader; exact mul_pos (mul_pos (mul_pos (mul_pos (pow_pos hP.scale _) he) ht) (pow_pos hx _)) (Real.exp_pos _)
lemma epilogue {x:(D).X}{z:(D).Y} (H : ∀ j:(D).S.Choices, Lapis.table (D).B j (D).T.up (D).T.high (x,p.shiftV x z)= Lapis.table (D).B J (D).T.up (D).T.high (x,p.shiftV x z))(h:p.utterance x z) :
    p.notion x (p.stainP x z)= p.outerP * p₀ (-β*Lapis.table (D).B J (D).T.up (D).T.high (x,p.shiftV x z)-Precision.loop (D).T.up (pul (D).B (x,p.shiftV x z))) := by
    let S:=(D).S; let a:=Lapis.table (D).B J (D).T.up (D).T.high (x,p.shiftV x z); let P:= pul (D).B (x,p.shiftV x z); let Z:=-β*a-Precision.loop (D).T.up P; have hA (i:S.Choices) : actU (D).B (D).T i p.budget β (Cove.ship x) (stainP p x z)=p.outerP*S.likelihood P i *p₀ Z := by
        erw [acts _ _ _ _ _ _ _ h, show mainTerm _ _ _+noiseTaylor S _ _ _ =_ from (show mainTerm (D).T.high (D).T.up P+noiseTaylor S (Cove.ship x) P i=a from H i)]; rfl
    change ∑ i:S.Choices,actU (D).B (D).T i p.budget β (Cove.ship x) (stainP p x z)=_; simp_rw [hA,← Finset.sum_mul, ← Finset.mul_sum, S.chosen hp.stitches.large.1,mul_one]; rfl
lemma leafV (x:(D).X)(z:(D).Y)(h: let y:= p.flag • x; let w:=stainP p y z; let v:=windmill (D).B (p.shiftV y z); v∈ mouth P ∧(p.utterance y z→ |p.poll ((D).B.drape w)|≤1 ∧ input G (D).f (Cove.lane (D).B (y,p.shiftV y z))=(D).B.drape w ∧ (∀ j:(D).S.Choices, Lapis.table (D).B j (D).T.up (D).T.high (y,p.shiftV y z)= Lapis.table (D).B (D).label (D).T.up (D).T.high (y,p.shiftV y z))))
     (he:∀ w,skel p.bench 3 w=(D).℘ w.1.2 + Junction.gram (D).B χ w.2):
     let y:= p.flag • x; let v:= p.shiftV y z; g^p.sizes * (Next.SectorChange.pay P (windmill (D).B v) * traceK p y (p.stainP y z)) = p.dream y * (Shield.lens₀ χ⁻¹ z *shadeV p x z):= by
    intro y v; let Yp:= p.stainP y z; have hv: Yp= om (D).B (y,v):=rfl; let U:=(D).B.drape Yp; have hU:U=pul (D).B (y,v):=rfl; obtain ⟨ha,h⟩:= h; unfold traceK shadeV; change _ =_*( _*(if p.utterance (p.flag • x) z then _ else _)); split;
    next hx=>
       obtain ⟨s,hU,H⟩:=h hx; let A:= worker p; let K:=p.crab x z; let a:= Angle.material (D).T.high (D).T.up g U; let d:= Lapis.table (D).B J (D).T.up (D).T.high (y,v); let f:= p.poll U; let Y':= Precision.loop (D).T.up U; let t:=Real.exp (-β*d-Y'+f); let Z':= biomass (f:=(D).f) k p.budget p.importB (D).T.high (D).T.up; let r:= Lapis.sumAt (D).B P v;
       rw [epilogue hp hP H hx]; change g^p.sizes * ( _ * (p.outerP * p₀ (-β*d-Y') * (p.quake U)))= _; unfold quake; rw [max_eq_right (Real.exp_monotone (abs_le.mp s|>.1)),min_eq_right (Real.exp_monotone (abs_le.mp s|>.2)), ray_meter P _ hP v ha]; change g^p.sizes * ( P.scale^_* Real.exp r * (p.outerP * p₀ (-β*d-Y') * p₀ f))=_
       have hℓ : 0<g ∧ g^2*β=1:=gS β hp.intake.positive; obtain ⟨B,hB,-⟩:=hp.service; have hm:= (Lapis.wakes (D).B J (D).T.up (D).T.high (D).ρ σ C _ B hp.stitches.large hp.staples hB 0 (by rw [norm_zero];exact hB.x_pos)).1
       have hx: p₀ (r+(-β*d-Y'+f)) = p₀ ( -β*(D).℘ y)*(p₀ (- Junction.gram (D).B χ z)*p.warm x z):= by
           have hv : g⁻¹ ^2=β := by have h:=hℓ.1; rw [inv_pow]; field_simp; linarith only [hℓ.2];
           let S:= shuttle (D).B (D).L K; have hU' : f=-(β*(Z' S)):= by
               unfold f StagePort.poll; rw [neg_mul]; apply congr_arg; apply congr_arg; unfold Z' biomass stake; refine sum_congr rfl fun i hi=> ?_; unfold conjunct; change _*Trio.froth _ U = g^i * Trio.froth _ (input G _ _); erw [show input G (D).f S.2=U from hU]
           have hY: p.natal K=d+g^2*(Y'-r)+Z' S:= rfl; unfold warm warmth hint; rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; apply congr_arg; rw [Pi.sub_apply,Pi.sub_apply,hv,he]; change _+(-β*d-Y'+f)= -(β)* _ + ( - Junction.gram (D).B χ z +( -(β)*(p.bench K-((D).℘ y+ Junction.gram (D).B χ (g • z)))+β* (p.bench K-_))) ; rw [hU',variation,hY];
           linear_combination ((-(Junction.gram (D).B χ z)+(Y'-r)))*hℓ.2 -- sign may
       have hl:= Junction.lens (D).B χ hm z; rw [hl] at hx; rw [Real.exp_add, Real.exp_add _ f] at hx; unfold dream grader; linear_combination P.scale ^ (Fintype.card (D).B.Free) * p.outerP * g^p.sizes * hx
    next hx=>
       unfold notion; rw [Fare.total,Pane.sparkling,if_neg (?_ : ¬ flags p.budget.threshold _ = ∅)]; ring; exact hx
end StagePort
end Provision
end YM.Contacts.Junction
