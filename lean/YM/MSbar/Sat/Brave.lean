import YM.MSbar.Sat.Burst
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{U:Config G f}{R:Rep G f}{σ C T a v y δ w D b u Δ μ ψ t₀:ℝ}{k n:ℕ}
open Finset YM.MSbar.Bulk SectorNext.Vacuum Precision Tree Pressure Pressure.Stores Push.Uniform
variable (F : Forest S.ratio)(J: Voice G)(p:Palisade)
     (i:S.Choices) (j:Key F G) (t:ℝ)(m:ℕ)
set_option quotPrecheck false
local notation "N"=> (Key F G)
local notation "H"=> priced F i R.clip R.path
local notation "L"=> address F G
local notation "X"=> shutterPad F G j m
local notation "x₀"=> crown F i j t m R
local notation "h!"=> pedal F x₀
local notation "k₀"=> ice p.coords p.gap p.a p.density
variable (x:Positions (Primary c G))(h:Grants i R F p n)(g:Clear G J) (hd: S.patch.Branches S.kernel G)
local notation "T!"=> R.p.threshold
local notation "V"=> represent (tint G _ x)
local notation "Y"=>halo (2*k) X
local notation "τ"=> excavation F Y T! b
variable (hA : Floss p J t u D t₀ v b a Δ ψ m)
    (htb: necklace S.patch≤k) (hv: represent (tint G (Exterior.Body 1 c) x) ∈ calm G c v) -- notation quote fails
    (hx: ‖x‖ ≤ a)(hb: bonfire F G (halo (2*k) (shutterPad F G j m)) (J.C*D) u≤ t₀)
variable {cF : ℝ} (hu:U∈excavation F (halo (2*k) (shutterPad F G j m)) R.p.threshold b)
set_option quotPrecheck false
local notation "W"=> chink F J V U Y
local notation "W'"=> chink F J V (pedal F (crown F i j t m R) U) Y
local notation "U!"=> exterior F J V U Y
local notation "V!"=> exterior F J V (pedal F (crown F i j t m R) U) Y
-- all pre V and witness.This regulator for weighted.A.Duty
variable (ρ:ℝ) (hy:Quasi R.eval ρ) (sold:Admitted (represent (tint G (Exterior.Body 1 c) x)) R S σ C δ T w)(hz:0≤ R.beta) -- Amb notation
open WilsonStartup
local notation "Q!" => hurry p (max a D) Δ ψ
local notation "A!" => outset R.p σ C δ T R.beta k (X).card
local notation "C!"=> Real.exp (ρ*(J.C*u)*(4*↑(X).card)+R.beta*(Δ*p.noise))
variable (hP:Psalm S R cF y)(L0:MergeProof.Menu.Arsenal R)
omit hP in
lemma untouched {n:Side}{U U':Config G n}{Z:Support n} (t:ℝ) (j : Site n) (he:j∉halo 4 Z)(h:Spine Z U U'): j∈flags t U ↔ j∈flags t U':= by -- synt
   simp_rw [flags_spec]; apply exists_congr; intro i; by_cases hd:j∈ RG.touched i
   swap; · simp [hd]
   have hi : Disjoint (RG.touched i) Z:= Finset.disjoint_left.mpr (fun p ht hx=> he (halo_spec.mpr ⟨p,hx,(separation_triangle p i.1 j).trans (show _≤4 from by
      have h1:=visit_near i ht; have h2:=visit_near i hd; rw [separation_comm j] at h2; omega)⟩))
   rw [show faceValue U i=faceValue U' i from face_local i U U' (h _ hi)]
def tailsSet (R:Rep G f) (p':ℝ) : Set (Config G f):= {U | p' < t*(fareX F J (represent (tint G _ x)) U j.1 j.2-vest (priced F i R.clip R.path) x j)}
set_option quotPrecheck false
local notation "M"=> tailsSet F J i j t x R
local notation "p!"=> chance S R V
include F k
lemma bangR : j.fst∈ board F Y:= Finset.mem_filter.mpr ⟨mem_univ _,halo_subset _ _ (halo_spec.mpr ⟨_,mem_singleton_self _,separation_self _ ▸ Nat.zero_le _⟩)⟩
include g
lemma fees (u:ℝ) : Seal S (youth F Y) (M u):=seals F J V g j.fst _ (bangR F j m)
variable (hK:2 ≤ k)(hw:R.p.B≤ k)(hQ : Decent R.clip R.p)(hc:Continuous R.eval)(hρ:∀ μ,0< R.eval μ)
variable (hs: flags cF (represent (tint G (Exterior.Body 1 c) x))=∅)(hq:0≤ y) {q u':ℝ}
include sold hz hd h hP L0 hy hA hv hs hq hK hw hc hρ hb htb hx hQ
lemma sheared (ha: p! (excavation (G:=G) F Y R.p.threshold b)ᶜ ≤ q) : p! (M u') ≤ Real.exp (A!+R.beta*(Q! -u')) * p! (M (u'-|t| *Δ))+ ((1+C!)*q+y*(R.p.mass (youth F Y) 2*Real.exp ((youth F Y).card*w))) :=by
   let X':=youth F Y; have hQ₀:=halo_subset (2*k) X
   refine tumble F (crown F i j t m R) hd sold hP L0 (fees (k:=k) F J i j t m x g u') (vital F Y T! b) (fees F J i j t m x g _) (aims F i j t m hQ₀) hc hρ hq hs ha (fun i' hi=> ?_) (Real.exp_pos _).le (Real.exp_pos _).le (fun u hc hd=> ?_) (fun i' hi hl hU=>?_)
   · exact budgetPress F J p _ j t m x h g hd hA htb hv hx hb hi ρ hy sold hz
   · ext j; by_cases hj:j∈Y
     · exact iff_of_false (fun he=> disjoint_left.mp hd.1 hj he) (fun he=> disjoint_left.mp hc.1 hj he)
     refine Iff.symm (untouched T! _ (fun h'=>hj (Corona.halo_mono (by omega : 4 ≤ 2*k) subset_rfl h')) (spine_in ?_))
     intro i hv; by_cases hx:i ∈ F.trunks
     · unfold pedal; rw [show F.drape _ i=1 from F.on_tree _ ⟨i,hx⟩]; group
     let j':F.Free:=⟨i,hx⟩; unfold pedal; have he:= F.off_tree x₀ j'; have ht:x₀ j'=1:= by_contra (fun hp=> hv (pages F _ _ _ _ j' hp)); rw [show F.drape _ i=1 from he.trans ht]; group
   let z:= i'; let f(w):=chink F J V w Y; have ht(w): f w j=fareX F J V w j.fst j.snd:=by change tint G _ (chink F J V w _) j.fst j.snd= _; rw [chink, ContinuousLinearEquiv.apply_symm_apply]; dsimp only; rw [if_pos (bangR F j _)]
   have hw : u'< t*(fareX F J V z j.fst j.snd-vest (priced F _ _ _) x j):= hi; refine ⟨?_,whirlwind F J p i j t m x h g hd hA htb hv hx hb hl sold hz hU ‹R.p.B≤ k› hQ hw.le⟩
   let v:= pedal F (crown F i j t m R) z
   have hz : ‖f v-f z‖ ≤ Δ:= (sup_wash _).trans (thistle F J p i j t m x h g hA htb hv hx hb hl|>.2.2.1)
   have hv':|t*(f v j-f z j)|≤|t| *Δ:=by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (f v-f z) j).trans hz) (abs_nonneg _)
   rw [ht,ht] at hv'; change u'-|t| *Δ < t*(fareX F J V v j.fst j.snd-vest (priced F _ _ _) x j); linarith only [hw,(abs_le.mp hv').1]
end YM.MSbar.Heath
