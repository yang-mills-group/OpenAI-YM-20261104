import YM.MSbar.Mosaic.Currencies
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X f' g:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k q L:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
local notation "λ'" i=> Cane.value (αm i) M.C M.A M.E M.s M.sway
-- Orientation host before-L relies eventually.C/4
noncomputable def Ore (M:StageCost)(x:ℝ)(P:Patch): Prop:= Cane.value (αm x) M.C M.A M.E M.s M.sway/P.L.val ≤ 1/128
variable (hR:∀ᶠ i in φ,Ore M (X i) K)
include hX hp hG hc hR hW
variable (P:Palisade)
-- avoid packaging by set invariant.Exterior.Real.S. Radius choose formula W^2 etc direct as functions.Time.
lemma sizes : ∃ r v:ι→ℝ, Run φ Y r 0 ∧Run φ Y v 0 ∧
     (∀ᶠ i in φ,let A':= A i; let z:= X i; let V:=tip G K.L z; let x:= hull z; let q:=topP J P V; let d:=room V
                 let L:=(A'.S.patch.L.val:ℝ); let t:=A'.fClock
                 1 ≤ r i∧ 1≤ v i ∧ x ≤ v i∧M.st2*x ≤ v i ∧ M.st2*x+(q+d)/t ≤ v i∧ shade G*(M.st2*x+(q+d)/t) ≤ r i∧shade G*(M.st1*x) ≤ r i∧ (λ' z)/L*x+(q+d)/t < vol V/4)∧ ∀ (b:ℝ),∀ᶠ i in φ,let A':= A i; let v':=tip G K.L (X i); let z:= X i;let y:=vol v'; b*A'.fClock*(r i)^2 ≤ y/4:=by
    let Xx:=X; let Y':=Y; let L':=(K.L.val:ℝ)
    let v(i):= vol (Y i); let k(i):=hull (X i); let q(i):= topP J P (Y i)+room (Y i); let Ty(i):=(A i).fClock; let U(i):= q i/Ty i; let S(i):= M.st2*k i+U i
    let r(i):= max 1 (max (shade G*S i) (shade G*(M.st1*k i))); let W'(i):= max (max (1:ℝ) (max (k i) (M.st2*k i))) (S i)
    have hu:Tendsto Y φ atTop:= (Work.E09.betaF_growth G K.L).comp hX
    have hk:Run φ Y k 0:= (Run.wander hX G hG K.L _ k).1 (((Run.stanza hX).mulY hX ((32:ℝ)⁻¹)).mulK hX 4); have hh : Run φ Y (fun i =>(Ty i)⁻¹) (1/2):= roundS hX J H H' K hG hp|>.2.1
    obtain ⟨hf,he,hZ,hB,hD⟩:= height hu P J; let q':=topP J P ∘ Y; have hf:Run φ Y q (-(1/2)):= (hD.loosen (by norm_num : (-1:ℝ) ≤ -(1/2))).addR hu he
    have hz:Run φ Y U 0:=by apply Run.loosen (hf.mulR hu hh); norm_num -- unfold U
    have hS:Run φ Y S 0:=(hk.mulK hu _).addR hu hz; have hr:Run φ Y r 0:=(Run.token hu _).Ymax hu ((Run.mulK hu hS _).Ymax hu ((hk.mulK hu _).mulK hu _)); refine ⟨r,W',hr,((Run.token hu _).Ymax hu (hk.Ymax hu (hk.mulK hu _))).Ymax hu hS,?_,?_⟩
    · have hb:Tendsto v φ atTop := (Alto.broad.comp hu).atTop_mul_const (r:=(32:ℝ)⁻¹) (by positivity); have he: Tendsto (fun i=> U i / v i) φ (𝓝 0):=by
           have h₁ : Run φ Y (fun i=> topP J P (Y i)/(Ty i*hatW (Y i))) ((-1:ℝ)+1/2):=by
                have hv':= Run.Yrat hu hh (Run.tempo hu); refine Run.alter (hD.mulR hu hv') (Eventually.of_forall (fun x=> ?_)); dsimp only [Function.comp_apply]; ring
           have h₂:= (tails hX J H H' K hG hp).mono (fun i hi=> hi.1)
           have he:= ((h₁.bouquet hu (by norm_num)).add (minimal hu h₂)).mul_const (32:ℝ); rw [add_zero,zero_mul] at he; refine he.congr' ?_; filter_upwards with i; unfold U v q Ty Mosaic.vol; ring
      filter_upwards [hp,hc,hR,hW, hX.eventually (Alto.drift_scale hG K.L), hb.eventually_gt_atTop 0,he.eventually (eventually_lt_nhds (show (0:ℝ) < 1/8 by norm_num)),hX.eventually_gt_atTop 1] with i hp ⟨hF,hQ,hS,hV⟩ hR hW H hv he hs A0 z V y u d L t
      let a:=(max (1:ℝ) (max (k i) (M.st2*k i)))
      unfold r W'; refine ⟨le_max_left ..,(le_max_left (1:ℝ) _).trans (le_max_left a _),(le_max_left (k i) _).trans ((le_max_right ..).trans (le_max_left a _)),(le_max_right (k i) _).trans ((le_max_right ..).trans (le_max_left a _)),le_max_right a _,(le_max_left ..).trans (le_max_right ..),(le_max_right ..).trans (le_max_right ..),?_⟩ -- last
      have hH:0 ≤ y:= (norm_nonneg _).trans hW; have hp':y≤4*v i:=mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right H.2.1 (by norm_num : (0:ℝ)≤32)) (by norm_num : (0:ℝ)≤4)
      have hx : L=L':=by unfold L L'; rw [show A0.S.patch=K from hp.space]
      have hP:U i < (1/8)*v i:= (div_lt_iff₀ hv).mp he
      rw [hx]; apply lt_of_le_of_lt (add_le_add_left (mul_le_mul_of_nonneg_right (show (λ' z)/L'≤1/128 from hR) hH) _); change 1/128*y+U i < v i/4; linarith only [hp',hP,hv]
    intro b; have hz:= (roundS hX J H H' K hG hp).1; let Uv(i):= b*Ty i*(r i)^2/(v i)
    have hk : Run φ Y Uv (-(1/2)):=by let f:= Run.tempo hu; apply Run.Yrat hu ((hz.mulK hu b).Yrat hu (hr.Ypow hu _)); unfold v Mosaic.vol; simp_rw [inv_div]; exact Run.mulK hu f _
    have hV : Tendsto v φ atTop:= (Alto.broad.comp hu).atTop_mul_const (r:=(32:ℝ)⁻¹) (by positivity); filter_upwards [hV.eventually_gt_atTop 0, (hk.bouquet hu (by norm_num)).eventually (ge_mem_nhds (show (0:ℝ)<1/4 by norm_num))] with i hi hP; exact ((div_le_iff₀ hi).mp hP).trans_eq (by ring)
end Issue
end YM.MSbar.Mosaic
