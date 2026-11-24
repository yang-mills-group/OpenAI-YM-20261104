import YM.MSbar.Sat.Angle
import YM.MSbar.Sat.Shelf
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
-- currency conditions monetary per sample
structure Floss (p:Palisade)(J:Voice G)(t u D τ0 v b Uγ Eκ r: ℝ)(M:ℕ) : Prop where
    bump : 0≤b
    arc : 0<v
    frock : shade G*(|t| * ice p.coords p.gap p.a p.density) ≤ u
    warmth : 0 ≤ u
    step : u≤D
    fill : J.C*(b+v/4) ≤ D
    roll : D ≤ J.r
    holds : J.C*u+(b+v/4) ≤ J.δ
    safe : max Uγ D+ Eκ < p.initial
    oil : τ0+|t| *ice p.coords p.gap p.a p.density≤Eκ
    amps : τ0+|t| *(Real.exp (-(tiltWidth p.coords (p.gap/2) p.a p.density/2)* M)*ice p.coords p.gap p.a p.density) ≤ r
variable (hA : Floss p J t u D t₀ v b a Δ ψ m)
    (htb: necklace S.patch≤k) (hv: represent (tint G (Exterior.Body 1 c) x) ∈ calm G c v) -- notation quote fails
    (hx: ‖x‖ ≤ a)(hb: bonfire F G (halo (2*k) (shutterPad F G j m)) (J.C*D) u≤ t₀)
variable {cF : ℝ} (hu:U∈excavation F (halo (2*k) (shutterPad F G j m)) R.p.threshold b)
set_option quotPrecheck false
local notation "W"=> chink F J V U Y
local notation "W'"=> chink F J V (pedal F (crown F i j t m R) U) Y
local notation "U!"=> exterior F J V U Y
local notation "V!"=> exterior F J V (pedal F (crown F i j t m R) U) Y
include h hA g hx hv hu hb htb
lemma thistle :
   Trail S X k (canoe F U) U! (canoe F (h! U)) V! ∧ ‖meetVar x W‖≤ max a D ∧ wash (W'-W) ≤ Δ ∧
    (∀ z, ‖braid F i j t m R z‖≤u) ∧ wash (W'-W+t • plank H j) ≤ ψ:=by
   let I:= W; let Z:= W'
   let A:= braid F i j t m R
   have hK i: ‖A i‖ ≤ u:= (masts F p _ _ _ _ h i).trans hA.frock
   have hs i: G.chord (G.lieExp (A i)) ≤ J.C*u:= ((g.small (A i) ((hK i).trans (hA.step.trans hA.roll))).2).trans (mul_le_mul_of_nonneg_left (hK i) (zero_le_one.trans g.cost))
   have he:= clears F V hv hA.arc U hu
   have hp : pays F V (J.C*u+(b+v/4)) Y (h! U):= dune F V U he _ hs
   have hz : b+v/4 ≤ J.δ:= (le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans g.cost) hA.warmth)).trans hA.holds
   have ht : ‖I‖ ≤D:= (sizing F J V g Y U he hz (by linarith only [hA.bump,hA.arc])).trans hA.fill
   have hF:=winding F J V x₀ (pages F i j t m) Y U
   let s:= scarf F i j t m R; let W₀:=Z-I
   have hζ:=bask F J p _ _ _ _ h g V hA.frock hA.roll hA.step he hz hA.fill (halo_subset (2*k) X)
   refine ⟨⟨hF.1,hF.2,apt F J V g _ U he hz,apt F J V g _ (h! U) hp hA.holds⟩,?_,?_,hK,?_⟩
   · rw [norm_meet]; exact max_le_max hx ht
   · have hh : W₀=W₀-s+s:= by abel
     change wash W₀≤ _; conv_lhs => arg 1; rw [hh];
     exact ((wash_add ..).trans (add_le_add (hζ.trans hb) (jewelled F p _ _ _ _ h))).trans hA.oil
   apply le_trans ?_ hA.amps; change wash (W₀+_) ≤ _
   let Az:=prime L m H j; let q:=plank H j; rw [show W₀+t • q=W₀-s+t • (q-Az) from ?_]
   · refine (wash_add  ..).trans (add_le_add (hζ.trans hb) ?_); rw [wash_smul]; exact mul_le_mul_of_nonneg_left (excess h.buys ..) (abs_nonneg _)
   change _= _ - (-t) • Az + t • _; simp only [smul_sub,neg_smul]; abel
-- Exact sori cumulative log.T.noise proof.Psi. Include root t moved. 
def sigh (S:StepData c f) (i:S.Choices)(Z:Config G c) (A B:Config G f) := noiseTaylor S Z A i-noiseTaylor S Z B i
include hd
lemma embossed :
   S.density R.beta U V=S.density R.beta (h! U) V*Real.exp (-R.beta * sigh S i V U! V!)∧
     |sigh S i V U! V!| ≤ Δ*p.noise:=by
   obtain ⟨hq,hR,hL,hM,hK⟩:= thistle F J p i j t m x h g hA htb hv hx hb hu
   let z:= meetVar x W; let w:=meetVar x W'; let D₀:= max a D; have ht : 0 ≤ Δ := (wash_nonneg _).trans hL; have hx : ‖W'-W‖≤ Δ:= (sup_wash _).trans hL
   have hp : z∈ball 0 p.initial:=mem_ball.mpr (by rw [dist_zero_right]; linarith only [hR,hA.safe,ht]) -- defeq
   have hz: ‖w‖ ≤ D₀+Δ:=by
      rw [show ‖w‖= max ‖x‖ _ from norm_meet ..]; rw [norm_meet] at hR; refine max_le ((le_max_left ..).trans (hR.trans (le_add_of_nonneg_right ht))) ?_
      have he:= norm_sub_le (W) (W-W'); rw [sub_sub_cancel,norm_sub_rev] at he; exact he.trans (add_le_add ((le_max_right ..).trans hR) hx)
   have hy: w∈ball 0 p.initial:=mem_ball.mpr (by rw [dist_zero_right]; exact hz.trans_lt hA.safe)
   have hΘ (i: Positions (Key F G)) : outer G F (meetVar x i)=V:=by unfold Push.Uniform.outer; rw [paint_meet]
   have hφ(z: Config G f) : fine G F (meetVar x (chink F J V z Y))=exterior F J V z Y:=by unfold fine; rw [paint_meet,hΘ]; rfl
   have hW (E:Config G f): S.density R.beta (canoe F E) V=S.density R.beta E V:=by rw [← S.covary hd (F.foldAt E) R.beta E V]; exact congr_arg _ (by funext; simp [Lattice.gauge,F.fold_root])
   constructor
   · rw [←hW U,← hW (h! U)]; refine payday S hd htb hq V (?_) (?_) i (fun k=>?_)
     · rw [← hφ]; exact h.enrollment _ hp
     · rw [←hφ]; exact h.enrollment _ hy
     have hB:= h.choice z (ball_subset_ball p.enroll hp) k; have hP:= h.choice w (ball_subset_ball p.enroll hy) k; unfold z at hB; unfold w at hP; rw [hφ,hΘ] at hB hP; exact congr_arg₂ (·-·) hB hP
   let F₀ v:=noiseTaylor S (outer G F v) (fine G F v) i
   have he := stream (f:=F₀) (p.first.trans_le p.enroll) ((by norm_num:1≤3).trans h.buys.order) p.costs.le (fun x hb=>h.weighs x hb) hR hx (hA.safe.trans_le p.enroll)
   rw [add_sub_cancel] at he
   unfold F₀ at he; rw [hφ,hφ,hΘ,hΘ] at he; unfold sigh; rw [abs_sub_comm]; exact he.trans (mul_le_mul_of_nonneg_right hL p.costs.le)
end YM.MSbar.Heath
