import YM.MSbar.Lapaz.Splash
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Lapaz
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
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
variable {q:ℕ} (g:ℝ→ℝ)(s:Site f→ G.Color) (hp: Lodge.Hat q w K g) (hv: ∀ x∈ Metric.closedBall (0:Positions (Primary f G)) w, ContDiffAt ℝ (↑(2:ℕ)) (film R H' t p) x∧ (∀ i:Primary f G,|fderiv ℝ (film R H' t p) x (bolt i)| ≤ D))
omit h ht hU
include hp hv
local notation "τ₀"=> recoil F R v J X Y U' t Z H' p s g
lemma rocky : Continuous (recoil F R v J X Y U' t Z H' p s g):=by
    let P':= τ₀; let j(i:X₀):= P! i; let V':=Lodge.Clamp (σ:=Primary f G) g; let D'(i:X₀):=V' (Tilt.regal s (j i) 1); have he:D'=(fun x=> V' (j x+grad s)):=funext fun x=>by unfold D' Tilt.regal; rw [one_smul]
    have hP:Continuous D':=by rw [he]; exact ((Lodge.hut hp).continuous.comp (Continuous.add ((stamp ..).continuous.comp (vertical ..)) continuous_const)); -- semicolon
    exact continuous_iff_continuousAt.mpr fun x=>(((hv (D' x) (Lodge.peak hp ((abs_nonneg _).trans (hp.value (0:ℝ)|>.2)) _)).1.continuousAt).comp hP.continuousAt)
noncomputable def inkW (N:ℕ)(G:Gauge)(w b:ℝ) := b*( ((N*G.lieDim:ℕ):ℝ)*(2*w))
lemma withinW (hD:0 ≤ D) : |recoil F R v J X Y U' t Z H' p s g x-τ₀ 0| ≤ inkW (keepF F X).card G w D :=by
    let Z':= Metric.closedBall (0:Positions (Primary f G)) w; let U(i:X₀):= Lodge.Clamp g (Tilt.regal s (P! i) 1); have ht:0≤ w:=(abs_nonneg _).trans (hp.value (0:ℝ)|>.2); have he(v:X₀): U v∈Z':=Lodge.peak hp ht _; apply (Tilt.allV _ Z' (convex_closedBall ..) (fun x hx=> (hv x hx).1.differentiableAt (by simp)) (fun x hx=>(hv x hx).2) (he 0) (he x)).trans; apply mul_le_mul_of_nonneg_left _ hD; have hv(j:Primary f G)(v:X₀): ‖U v j‖≤w:=(norm_le_pi_norm _ _).trans (mem_closedBall_zero_iff.mp (he v)) -- mem
    apply Tilt.tin (keepF F X); · exact Finset.sum_nonneg fun i _=> zero_le_one
    · intro i hi; have ht: P! x i=P! 0 i:=by apply congr_arg (fun v:G.Color=>v i.2) (pupil F R v J X Y U' t Z 0 x i.1 hi)
      unfold U Lodge.Clamp Tilt.regal; rw [Pi.add_apply, Pi.add_apply,ht]
    exact fun i=> (abs_sub (U x i) (U 0 i)).trans ((add_le_add (hv i x) (hv i 0)).trans_eq (two_mul _).symm)
omit hp hv
local notation "x₁"=> L! (0:X₀)
variable {b0 Λ':ℝ}{m0 y' :ℕ}
lemma baro (T':PowerSeries (Pot (Joint F G)))(m:ℕ)(α:Site f)(a:ℝ)(ha:∀ i≤p,Vault (address F G) {α} a y' m 0 (PowerSeries.coeff i T') b0 ∧ (PowerSeries.coeff i T').totalDegree ≤ m)(hx: ‖meetVar Z (berth F R v J X Y U' Z t 0)‖ ≤ Λ')(hv:0 ≤ a):
      Belt p (micro (x₁) (vene X F G) T' x) ≤ barry 0 m p b0 Λ'*(1+‖x‖)^(m+2):=by
      let W':=vene X F G; let z:= x₁; let z' := z+W'*ᵥ x; have ht : ‖z'‖ ≤ Λ'+‖x‖:= (norm_add_le ..).trans (add_le_add hx (vision F X x)); have hb:0≤ b0:=ha _ le_rfl|>.1.1; let L:= Λ'+‖x‖; have hL:0≤Λ':=(norm_nonneg _).trans hx; have hx : Belt p (picture z' T') ≤ barry 0 m p b0 L:=by apply Bout.beltR F p α T' z' hv ht (s:=y') (a:=a) ha -- args order
      apply hx.trans; unfold barry L; nth_rw 1 [show (p+1:ℕ)=_ from rfl]; rw [mul_assoc (↑(p+1:ℕ):ℝ),mul_assoc b0]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply mul_le_mul_of_nonneg_left _ hb; calc
            _ ≤ ((1+Λ')*(1+‖x‖))^(m+1):=by gcongr; nlinarith only [mul_nonneg hL (norm_nonneg x)]
            _ ≤ _:=by rw [mul_pow]; gcongr; exact le_add_of_nonneg_right (norm_nonneg _); omega
end YM.MSbar.Lapaz
