import YM.Integration.FVA1Physical.Sources.Round2.MeasuredSalary

/-! The genuine physical source error in a normalized conditional RG step is paid once,
independently of the ledger used for the interacting action. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open YM.MSbar YM.MSbar.Lapaz
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior YM.Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
variable {G:Gauge}{c f:Side} {S:StepData c f}(F:Forest S.ratio)(R:Rep G f)(v:S.Choices)(J:Voice G)(Q:Palisade)(χ:ChartRatio G)
local notation "V"=>Primary c G
local notation "P0"=>Key F G
local notation "G!"=>Joint F G
local notation "T"=>Positions (Joint F G)
local notation "x!"=> Positions (Primary c G)
local notation "Ω"=> address F G
local notation "H"=>mold R F v
variable (X Y:Support f)(U':Config G f) (t:ℝ)(Z:Positions (Primary c G))
local notation "Λ"=> includeX (G:=G) F X
local notation "X₀"=>SpaceP F X G
local notation "χ!"=>(pinch (includeX (G:=G) F X) H)⁻¹
variable (e:PathData G)(l:Clip)(ρ:fieldDir G c 1→ AxisChart G F)
local notation "ν"=>vest (priced F v R.clip R.path) (t • Z)
local notation "f1"=>linCash F (t • Z)
open Next.SectorChange
local notation "I!"=>hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "r₀"=>rental F J R Y v (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "c!"=> sampleY F R v J X Y U' (t • Z)
local notation "µ"=> c! ∘ includeX (G:=G) F X
local notation "A!"=> berth F R v J X Y U' Z t
variable {A B d C P D K w E:ℝ} (h:Suite J χ F X Y (postcard G c t Z) v R (vest (priced F v R.clip R.path) (t • Z)) A B d C P D (linCash F (t •Z)))
local notation "S!"=> clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U'
local notation "D!"=> Bakery.Film.draw F X U' (c! ∘ includeX F X) t
local notation "F!"=> fun z:SpaceP F X G=> fLog F X χ t z (c!∘ includeX F X) U' r₀ (show Matrix (Lake F X G) (Lake F X G) ℝ from (pinch (includeX F X) H)⁻¹)
variable (ht:0<t)(u x:SpaceP F X G)
include ht
local notation "Q₀"=> chambers F Y J (postcard G c t Z) ν
local notation "W"=> postcard G c t Z
variable (hU:U'∈ hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z)) A B)
include h hU
local notation "L!"=> fun z:X₀=> meetVar Z (A! z)
local notation "P!"=> fun z:X₀=> stamp F G (A! z)
local notation "θ"=> swung F χ
local notation "φ"=> pushChart F G v
variable (H':Nesting G f) (p:ℕ)
variable (M:Ages) (f':Config G f → ℝ)(g:ℝ→ℝ)(s:Site f→ G.Color)
local notation "Δ!"=> fun x:SpaceP F X G=> recoil F R v J X Y U' t Z H' p s g x -recoil F R v J X Y U' t Z H' p s g 0
local notation "τ!"=> vene X F G
local notation "δ"=> Lapaz.cov (C:=χ!) (vene X F G)
local notation "c'"=> keepB F X G
local notation "c0"=> keepF F X
local notation "Q'"=> barbed F v χ H'
local notation "Z'"=> meetVar Z (A! 0)
local notation "nM"=> Fintype.card (Lake F X G)
local notation "q'"=> micro (Z') (vene X F G)
local notation "r1"=>purse S! (fun x:SpaceP F X G=> F! x-F! 0)
variable (hp:X ⊆ Y) (hL:LocalRatio χ)(hg:Clear G J)(ht':t ≤ 1)(hQ:Kind H') (η:SpringK (Joint F G)) (hE:RG.Envelope f')
include hp hL hg ht' hQ hE
variable (A':Salary) {w' ε : ℝ}
theorem additive_ratio (fund : ℝ) (hc : 0 ≤ fund)
      (he:GaugeLocal S (youth F Y) r₀) (hδ: ∀ i:Lake F X G,χ! i i ≤ A'.δD)
      (hΩ : (fieldLaw χ!).real S!ᶜ ≤ A'.ρ)(hy: 0 < A'.ξ)
      (hM:∀ i: SpaceP F X G,Belt p (micro Z' (vene X F G) (Rewind Q' Z') i) ≤ A'.payQ*(1+‖i‖)^A'.m ∧ Belt p (micro Z' (vene X F G) η i) ≤ A'.payH*(1+‖i‖)^A'.m)
      (h₀:Measurable (recoil F R v J X Y U' t Z H' p s g))(hB:∀ i:SpaceP F X G,|recoil F R v J X Y U' t Z H' p s g i -recoil F R v J X Y U' t Z H' p s g 0|≤ A'.payΔ)
      (hτ: t*A'.payP ≤ A'.mark)(hν:∀ i:SpaceP F X G,i∈S!→Belt p ((q') (Rewind Q' Z') i) ≤ A'.payP ∧ Belt p ((q') η i) ≤ A'.payT)
      (hl:∀ i:SpaceP F X G,i∈ S! → |(F! i-F! 0)- (taste p (picture (L! i) Q') t - taste p (picture Z' Q') t)- (Δ! i)|≤ w')
      (hξ:∀ i:SpaceP F X G,i∈ S!→|f' (D! i)-taste p (picture (L! i) η) t| ≤ ε) (hϕ:t*(cloudK nM p A'.m A'.δD A'.payQ)+A'.payΔ +A'.nameP w' p nM t ≤ 1/2):
       |Rota.resample F (board F X) (woolModel F X J R Y v W ν A B) (I! A B) f' U' - localW F R v J χ X Y U' t Z H' p g s η| ≤ ε + Salary.stamp A' p nM t w' fund := by
       let G₀:Matrix (Lake F X G) (Lake F X G) ℝ:=χ!; have hC:G₀.PosDef:= (h.positivity.submatrix (secureY F X G)|>.inv)
       have hv':Kind (Q'):= well F v χ H' hQ
       obtain ⟨hS,hF,hA,hG,hTxx⟩:= swing F R v J χ X Y U' t Z h ht hU hL hp hg f' hE he
       let K₁:= Δ!; let F₁:= barbed F v χ H'; let v0(i:X₀):= F! i-F! 0; let H1(i:X₀):=f' (D! i)
       have hQ':=quilt τ! (p:=p) hC hδ F₁ η Z' hv' hM K₁ (h₀.sub_const _) hB hS hΩ hy ht.le ht' v0 H1 hF hA hG hτ hν (a:=w') (b:=ε)
       have hw:= hQ' (fun i hi=> ?_)
       swap
       · rw [show taste p (micro _ _ _ _) _= _ from (rebate F R v J X Y U' t Z i p Q').symm, micro, ← venue]; exact ⟨hl i hi,hξ i hi⟩
       have he0:(0:X₀)∈ S!:=born F R v J χ X Y U' t Z h ht hU
       have meas : Measurable (fun v:X₀=>taste p (micro Z' τ! η v) t) := by
         unfold taste
         exact Finset.measurable_sum _ fun i _=>(Lapaz.pic τ! Z' η i).const_mul _
       obtain ⟨exactField,lip⟩:=measured_salary (fieldLaw G₀) S! _ _ H1 v0 K₁ p _ _ _ _ _ _ _ _ _ fund hw ⟨_,he0⟩ hc meas
       rw [hTxx]
       exact (abs_sub_le _ _ _).trans (add_le_add lip (Lapaz.outfits τ! hC hδ F₁ η Z' hv' hM K₁
         (h₀.sub_const _) hB hS hΩ hy ht.le ht' v0 _ exactField ⟨_,he0⟩ hϕ))
end YM.Integration.FVA1Physical.Round2.Curvature
