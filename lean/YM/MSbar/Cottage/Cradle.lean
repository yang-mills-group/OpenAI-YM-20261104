import YM.MSbar.Cottage.Rental
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {U: Config G f}{R: Rep G f}{σ C T H K A B a b v r δ w β:ℝ}{M k m:ℕ}
open Finset RG.PathData Tree Push.Uniform Pressure
variable (F:Forest S.ratio) (X :Support f)
open SectorNext.Vacuum AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock Metric
variable (J:Voice G) (Q: Config G c) (μ: Positions (Key F G))(Y:Support f)
set_option quotPrecheck false
local notation "I!"=> IV F (board F X) G
local notation "U!"=> Config G f
local notation "q!"=> twirl (G:=G) (S:=S) F (board F X)
local notation "o!"=> fence F (board F X) G
-- exponent log model BEFORE HAAR (use project Jacobian later)
variable (i:S.Choices)(p:Palisade)(x: Positions (Primary c G)) (h:Grants i R F p m)
local notation "W"=> (represent (tint G (Exterior.Body 1 c) x))
local notation "Y!"=> hotel F X Y J W μ A B
local notation "z!"=> chambers F Y J W μ
local notation "f!"=> rental F J R Y i W μ
local notation "L"=> (R.exponent ∘ z!)
local notation "Ω!"=> priced F i R.clip R.path
local notation "R!"=> R.p.threshold
-- Choice.Posture quantity ∆. `B` bandwidth and K full bounds
local notation "h!"=>Posture p J F A B v K M k X Y x μ R.p
variable (g:Clear G J) (q:Posture p J F A B v K M k X Y x μ R.p)
namespace Posture
variable {p J F X Y x μ}
include q
-- numeric frame.K. Y copy. Healthy flags.Read extra halo
local notation "Ik"=> youth F Y
local notation "Uθ"=> "+unused"
local notation "E'"=> (silkRoad C σ δ T R.beta X.card M R.p k)
variable (t:I!) (sold:R.Lawful σ C T δ w)(hD:S.patch.Branches S.kernel G)(hB: Decent R.clip R.p)(hz:0≤ R.beta)
include g
omit g q in
def moss (G:Gauge)(r:ℝ)(Y:ℕ):=((r/4)^(Module.finrank ℝ G.Mat))^Y
omit g q in
def gardenCity (P:Palisade)(J:Voice G)(K r B:ℝ) := 0<r ∧ r ≤ J.δ ∧ J.C*r ≤ shade G*K ∧ J.C* (shade G*K)* (J.C*r)+J.C*r ≤ B ∧ J.C* (shade G*K)+r ≤ J.δ
lemma spruces (hU:U∈Y!)(hr:r≤ 1)(hu : gardenCity p J K r B) : moss G r (board F X).card ≤ (fence F (board F X) G).real ((fun t: I! =>twirl F (board F X) t U) ⁻¹' hotel F X Y J W μ A B) :=by
    let z:=Y!; let P: Set (IV F (board F X) G):=(fun t=> twirl F (board F X) t U) ⁻¹' z
    let j:= W; let Y₀(i:↥(board F X)):= flume F j U i.val
    let u:= r; let I:=board F X; let X':=(IV F I G); let a:= tint G _ μ; let C':= J.C* (shade G*K)*(J.C*r); let Y'(i):= G.lieExp (a i); let R'(t:X'):= twirl F I t U
    let M':X':=fun i=> Y' i.val*(Y₀ i)⁻¹; let D:= Set.pi (Set.univ:Set ↥I) (fun i=>G.shell r)
    obtain ⟨hx1,hx2,hx3,hx4,hx5⟩:=hu; let Xk:=shade G*K
    have hu':0 ≤ J.C:=zero_le_one.trans g.cost; have hh(z): ‖a z‖ ≤ Xk:= (norm_le_pi_norm (tint G _ μ) z).trans ((tint_le μ).trans (mul_le_mul_of_nonneg_left (le_trans q.seats (sub_le_self _ q.height)) (shade_pos G).le))
    have hs(t:X')(hP:t∈D)(i:F.Free)(hi:i∈board F X): R' (t*M') ∈ basin F J W μ i B:=by
        let p': ↥I:=⟨i,hi⟩; let y:= Y' i; have ht:G.chord (t p') ≤u:=hP p' (Set.mem_univ _); let f:=J.decode (t p'); have hh':‖f‖ ≤ J.C*u:= ((g.near _ (ht.trans hx2)).2.2).trans (mul_le_mul_of_nonneg_left ht hu'); have hp':‖f‖ ≤ Xk:=hh'.trans hx3
        have hg: flume F W (R' (t*M')) i=t p'*y:=by
            unfold R' flume twirl; rw [stationary,mul_assoc]; change pegged F I (t*M') i * (Y₀ p')=_
            rw [pegged]; rw [dif_pos hi]; change (t p' * (y*(Y₀ p')⁻¹))*_= _; group
        have H₀ :G.chord (flume F W (R' (t*M')) i)≤ J.δ:=by
            rw [hg]; have hk:G.chord y ≤ J.C*Xk:= ((g.small _ ((hh i).trans q.smoke)).2).trans (mul_le_mul_of_nonneg_left (hh i) hu')
            exact (G.chord_triangle ..).trans ((add_le_add ht hk).trans ((Eq.trans_le (by ring : u+J.C*Xk=J.C*Xk+u) hx5)))
        have ht': fareX F J W (R' (t*M')) i= J.decode (G.lieExp f* G.lieExp (a i)):=by unfold fareX; rw [hg,show G.lieExp f = t p' from (g.near _ (ht.trans hx2)).2.1]
        let Yx:= fareX F J W (R' (t*M')) i - a i
        have hX :‖Yx‖ ≤ B:=by
            have hi:= (g.turns f (a i) Xk q.smoke hp' (hh i))
            have he: ‖Yx-f‖≤ C':= by
                rw [show Yx-f=(J.decode (G.lieExp f* G.lieExp (a i)))-f-(a i) from ?_]; · exact hi.trans (mul_le_mul_of_nonneg_left hh' (mul_nonneg hu' ((norm_nonneg _).trans hp')))
                unfold Yx; rw [ht']; abel
            apply le_trans (le_of_eq (show ‖Yx‖=‖Yx-f+f‖ from (congr_arg norm (sub_add_cancel ..)).symm)); exact (norm_add_le ..).trans ((add_le_add he hh').trans hx4)
        exact ⟨(g.near _ H₀).2.1,fun j=>(PiLp.norm_apply_le Yx j).trans hX⟩
    have ht : D ⊆ (fun t:X'=>t*M') ⁻¹' P:=by intro t hh; exact ⟨hs t hh,(safezone F X Y J W μ g q.extendsX (t*M')).2 hU.2⟩
    have he := (climber F I G M'); have hp : MeasurableSet P:= (garden_main F X Y J W μ g q.extendsX|>.from_here).preimage (((twirlD F (board F X) G).comp (continuous_id.prodMk continuous_const)).measurable) -- placeholder
    have hR : (fence F (board F X) G).real ((fun t:X'=> t*M') ⁻¹' P)=(fence F (board F X) G).real P:=he.measureReal_preimage hp.nullMeasurableSet
    change _ ≤ (fence F (board F X) G).real P; rw [← hR]; apply le_trans _ (measureReal_mono ht)
    unfold fence moss D; rw [measureReal_def,Measure.pi_pi,prod_const,card_univ,ENNReal.toReal_pow]
    have ht : (Fintype.card ↥I)= (board F X).card:= by simp [I]
    rw [ht]; exact pow_le_pow_left₀ (by positivity) (G.shell_ge _ hx1 hr) _
end Posture
end YM.MSbar.Heath.Cottage
