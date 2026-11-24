import YM.FVA2.GridBirth
/-!
# Also identify the actual `offset β` charts of the separate Descent.ranking prescription.
 Not requiring estimated Recoil prices even at Step.Progress regional spheres. If actually
 comparing using that prescription's literal ASYMPTOTIC (not now), supply fixed-volume
 conditions and continuity etc. This uses α:Tag not mixing source.K.Income proof in next.
 Extends after all unmarked vacuums, *relative to the full period normalization*, not
 PhysicalSum directly! Only our inversion MS bridge affects that.
-/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.FVA2.CityHistory.Delay
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage Legacy
open MeasureTheory.Measure (IsAddHaarMeasure)
open PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
lemma carry_center (x:ℝ): carry (E:=E) X=X∧ carry (E:=E) (C x)=roll x:= ⟨ PowerSeries.map_X _, Eq.trans (PowerSeries.map_C ..) rfl ⟩
lemma exp_vac0 {f:E→ℝ}(h:Radial.Stationary f): (pay 1 f) = advancing f := by
    refine sub_left_inj.mp (X_pow_mul_injective (Eq.trans (?_ : X^2 * (pay 1 f - C (coeff 2 (rise f))) = -(rise f)) ?_));
    · rw [upright_pay 1 h (map_one _),map_one,one_mul]
    -- supply other equal
    unfold advancing; rw [add_sub_cancel_right]; change - _ = X^2 * _; rw [Stack.recover ]; intro i hi; rw [map_neg,Fares.overdue f h i hi, neg_zero ]
end

def stones (u:ℕ→ℝ)(i:ℕ): PowerSeries ℝ:= 1 + X^2 * C (u i)
def exact_offset (t:ℝ)(b:ℝ) := t^2* b+1 -- not use. parser
lemma stone_parent (u:ℕ→ℝ): stones (upβ u)= parentZ (stones u):=rfl
lemma atOffset (u): SoundZ (stones u):= fun i=> by simp [stones]
variable (S:StepData c f)(T:Forest S.ratio)(d:Descent n f)(t:d.Tags)(b:S.Choices)
local notation "Φ"=> partΧ G S T d
local notation "φ"=> partΥ G S T d
local notation "F₀"=> (consume d t (G:=G))
lemma on_variable (g:ℕ→ℝ)(x:SpaceF G (Descent.push S T d)): consume ( Descent.push S T d ) ( show (Descent.push S T d).Tags from (b,t) ) g x= consume d t (upβ g) (Φ x)+ (g 1) * tax S T b (φ x):= at_step S T d t b g x

lemma pay_add {z v:ℕ→PowerSeries ℝ} {c:Side}(d: Descent n c)(t:d.Tags) : moneyX (G:=G) d t (z+v)=moneyX d t z+moneyX d t v:= by
     induction d generalizing z v with
     | nil=> rw [ moneyX,moneyX,moneyX,Pi.add_apply,map_add,add_mul,map_add ]
     | @push c f S T d ih=> rw [moneyX,moneyX,moneyX, show parentZ (z+v)=parentZ z+parentZ v from rfl, Pi.add_apply,map_add (Stack.carry (E:=Future G S T × Pins G c)), add_mul, ih, map_add,map_add (boost (partΥ G S T d)) ]; abel
lemma payX₂ (q:ℕ){z:ℕ→PowerSeries ℝ} {c:Side}(d: Descent n c)(t:d.Tags): moneyX (G:=G) d t (fun i=> X^q*z i)=X^q * moneyX d t z:= by
     have hz {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]: Stack.carry (E:=E) X=X:= PowerSeries.map_X _
     induction d generalizing z with
     | nil=> rw [moneyX,moneyX,map_mul (Stack.carry (E:=Pins G n)),_root_.map_pow Stack.carry,hz, mul_assoc, Shipment.boost_X]
     | push S T d ih=> rw [moneyX,moneyX, map_mul (Stack.carry (E:=Future G S T × Pins G _)), _root_.map_pow Stack.carry,hz,mul_assoc ( X^q ),Shipment.boost_X, show parentZ (fun i=> (PowerSeries.X ( R:=ℝ ) )^q*z i)=fun i=>X^q*parentZ z i from rfl,ih,Shipment.boost_X,mul_add ]

lemma pure_amount {c:Side}(d:Descent n c)(t:d.Tags)(b:ℕ→ℝ)(h:d.OK G): moneyX (G:=G) d t (fun i=> C (b i))=rise (consume d t b):= by
   induction d generalizing b with
   | nil=> rw [ moneyX, (carry_center (E:=Pins G n) (b 0)).2, ← ExactTower.rise_natural (b 0) ((born_hot G n).of_le le_top), FormalOPE.RG10.MarkovChain.Vault.climbing _ (show ContDiffAt ℝ ∞ (b 0 • bareF G n) 0 from (((born_hot G n).of_le le_top).const_smul (b 0))), show consume ( G:=G ) ( Descent.nil (top:=n) ) t b= ( (b 0) • bareF G n ) ∘ LinearMap.snd ℝ _ _ from funext ( fun _=>rfl ) ]
   | @push c f S T d ih=>
       rcases t with ⟨k,t⟩; let hq : d.OK G:= h.2; let M:= consume d t (upβ b) ( G:=G ); let F: Future G S T × Pins G c → ℝ:= ( b 1 ) • tax S T k
       have hF: ContDiffAt ℝ ω F 0 := (tax_hot S T k h.1).const_smul ( b 1 ); have he:= thermal d t hq (upβ b)
       rw [ moneyX ]; change boost (partΧ G S T d) (moneyX d t ( fun i=> C ( upβ b i ) ))+ ( boost (partΥ G S T d) ( carry ( C ( b 1 ) ) * _ ) )=_; rw [ih t (upβ b) hq, ( carry_center (E:=Future G S T × Pins G c) (b 1) ).2, ← ExactTower.rise_natural (b 1) (( tax_hot S T k h.1 ).of_le le_top ), FormalOPE.RG10.MarkovChain.Vault.climbing _ (he.of_le le_top),FormalOPE.RG10.MarkovChain.Vault.climbing _ (hF.of_le le_top), show consume ( G:=G ) _ _ b= M ∘ (partΧ G S T d) + F ∘ (partΥ G S T d) from (?_) ];
       · exact (ExactTower.up_add (( OpenSlots.leaned _ he|>.of_le le_top)) (( OpenSlots.leaned _ hF|>.of_le le_top ))).symm
       exact funext ( on_variable S T d t k b )

lemma displaced {c:Side}{d:Descent n c}(t:d.Tags)(b:ℕ→ℝ)(h:d.OK G): moneyX (G:=G) d t (stones b)=rise (consume d t 1)+ X^2 * rise (consume d t b):= by
   rw [ show stones b= 1+(fun i=>X^2*C (b i)) from rfl,pay_add,ordinary h, payX₂,pure_amount d t b h ]
lemma pays {c:Side}{d:Descent n c}(t:d.Tags)(b:ℕ→ℝ)(h:d.OK G): entryPay (G:=G) d t (stones b)= pay 1 (consume d t 1)-rise (consume d t b):= by
   obtain hp:= issueZ h t ( stones b ) ( atOffset b ); obtain hs:= upright_pay 1 (thermal_stat d t h) (map_one _); let F:= consume d t 1 (G:=G); let R:= rise (consume d t b ( G:=G )); -- fix
   rw [map_one,one_mul] at hs; rw [ displaced t b h ] at hp; apply ( sub_left_inj ).mp (X_pow_mul_injective (hp.trans (?_))); change - ( rise F+ X^2 * R )= X^2*(pay 1 F-R - C _); rw [ sub_right_comm, mul_sub, hs ]; abel
variable (Z:ChartRatio G)
lemma suitcase {c:Side}{d:Descent n c}(t:d.Tags)(b:ℕ→ℝ)(h:d.OK G)(hz:LocalRatio Z): supplyZ d Z t (stones b)= (supplyZ d Z t 1)*rise (Real.exp ∘ ( -(consume d t b))):= by
    let V:= consume d t b (G:=G); let V0:= consume d t 1 ( G:=G ); have he: (-V) 0=0 := (by simp [V, thermal_zero d t h]); have hp: ContDiffAt ℝ ∞ (-V) 0:= (thermal d t h b|>.of_le le_top).neg; have hx := ExactTower.rice hp he; rw [ Legacy.money Z hz h,pays t b h, Legacy.noStats Z hz h,←hx];
    have hv: -rise V=rise (-V):= by
        have hp':ContDiffAt ℝ ∞ V 0:= (thermal d t h b).of_le le_top
        have he:= ExactTower.up_add hp' hp; rw [add_neg_cancel,ExactTower.up_zero] at he; exact (eq_neg_of_add_eq_zero_right he.symm).symm
    rw [sub_eq_add_neg, show -rise (consume (G:=G) d t b)=rise (-V) from hv, compose_two _ _ ( stipend 1 _ (thermal_stat d t h) ) (ExactTower.rose_zero he) ]; exact ( mul_assoc .. ).symm
end YM.FVA2.CityHistory.Delay
