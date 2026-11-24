import YM.MSbar.Cottage.House
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
def rental (R:Rep G f)(Y:Support f)(i:S.Choices)(Q:Config G c)(μ:Positions (Key F G))(U:Config G f):= R.exponent (chambers F Y J Q μ U) - R.beta*noiseTaylor S Q (chambers F Y J Q μ U) i
variable (i:S.Choices)(p:Palisade)(x: Positions (Primary c G)) (h:Grants i R F p m)
local notation "W"=> (represent (tint G (Exterior.Body 1 c) x))
local notation "Y!"=> hotel F X Y J W μ A B
local notation "z!"=> chambers F Y J W μ
local notation "f!"=> rental F J R Y i W μ
local notation "L"=> (R.exponent ∘ z!)
local notation "Ω!"=> priced F i R.clip R.path
local notation "R!"=> R.p.threshold
-- Choice.Posture quantity ∆. `B` bandwidth and K full bounds
structure Posture (p:Palisade)(J:Voice G)(F:Forest S.ratio)(A B v K:ℝ) (M k:ℕ)(X Y:Support f)(x:Positions (Primary c G))(μ:Positions (Key F G))(b:BudgetPoint):Prop where
    stays : 0<A
    goes : A ≤ B
    seats : ‖μ‖ ≤ K-B
    awake : ‖x‖ ≤ K
    folds : represent (tint G (Exterior.Body 1 c) x) ∈ calm G c v
    lights : 0<v
    room : K+2*B < p.initial
    smoke : shade G*K ≤ J.r
    clean : 4*(J.C*(shade G*K)+v/4) ≤ b.threshold
    stone : b.B ≤ M
    crest : halo (2*M+8) X ⊆ Y
    solid : necklace S.patch≤ M
    bank : deepCopy b k ≤ M
-- posture buys.Log.Track.
local notation "h!"=>Posture p J F A B v K M k X Y x μ R.p
variable (g:Clear G J) (q:Posture p J F A B v K M k X Y x μ R.p)
namespace Posture
variable {p J F X Y x μ}
include q
lemma extendsX : X⊆Y := (halo_subset _ _).trans q.crest
lemma gazes : halo (2*M) X ⊆ Y:= (Corona.halo_mono (Nat.le_add_right ..) subset_rfl).trans q.crest
lemma height : 0 ≤ B:=(q.stays.le.trans q.goes)
lemma crestCast (t:IV F (board F X) G):t=t:=rfl
-- numeric frame.K. Y copy. Healthy flags.Read extra halo
local notation "Ik"=> youth F Y
local notation "Uθ"=> "+unused"
local notation "E'"=> (silkRoad C σ δ T R.beta X.card M R.p k)
variable (t:I!) (sold:R.Lawful σ C T δ w)(hD:S.patch.Branches S.kernel G)(hB: Decent R.clip R.p)(hz:0≤ R.beta)
include g
lemma pose (hU:U∈Y!) :
   ‖rented F Y J W μ U‖≤ K∧‖meetVar x (rented F Y J W μ U)‖≤ K∧ Agrees Y (canoe F U) (z! U) ∧ flags R.p.threshold (z! U)=∅ ∧ Healthy R.p.threshold (halo (2*M) X) (canoe F U):=by
    let V:= W; let a:= rented F Y J W μ U; let A:=canoe (S:=S) F U; have hl := leanOn F X Y J V μ g q.extendsX hU q.goes q.height; have hk : ‖a‖ ≤ K:= by
        rw [show ‖a‖= ‖a-μ+μ‖ from (congr_arg norm (sub_add_cancel a μ)).symm]
        exact ((norm_add_le ..).trans (add_le_add hl q.seats)).trans_eq (by ring)
    have hm:=cognizant F X Y J V μ g q.extendsX hU q.goes; have hv: flags R.p.threshold (z! U)=∅:= by
        refine voids (r:=4*(J.C*(shade G*K)+v/4)) ?_ q.clean; have hC:0 ≤ K:=(norm_nonneg _).trans hk
        have hK(d : Edge (Site f)): G.chord (Precision.replica S.ratio V d) ≤ v/4:=by unfold Precision.replica; split; rw [G.chord_one]; exact div_nonneg q.lights.le (by norm_num); exact q.folds _ (Set.mem_univ _)
        have hz: 0 ≤ J.C:=zero_le_one.trans g.cost
        intro j h'; change G.chord (z! U j) ≤ 4*(J.C*(shade G*K)+v/4)/4; unfold chambers lifting; by_cases hi:j∈ F.trunks
        · rw [show ∀ W':F.Slice G,F.drape W' j=1 from fun W'=>F.on_tree W' ⟨j,hi⟩,G.chord_one]; have hi:= shade_pos G; have h':= q.lights; positivity
        let u:F.Free:=⟨j,hi⟩; rw [show ∀ W':F.Slice G, F.drape W' j=W' u from fun W'=> F.off_tree W' u]; let w:= tint G _ a u; change G.chord (G.lieExp w * _ ) ≤ _
        have he: ‖w‖ ≤ shade G*K:= (norm_le_pi_norm (tint G _ a) u).trans ((tint_le a).trans (mul_le_mul_of_nonneg_left hk (shade_pos G).le))
        exact ((G.chord_triangle ..).trans (add_le_add (((g.small w (he.trans q.smoke)).2).trans (mul_le_mul_of_nonneg_left he hz)) (hK j))).trans_eq (by ring)
    refine ⟨hk,norm_meet x _ |>.trans_le (max_le q.awake hk),hm,hv,?_⟩
    let P:=halo (2*M) X; have hs : Healthy R.p.threshold P A:=by
        unfold Healthy; rw [disjoint_iff_inter_eq_empty]; rw [flags_agree R.p.threshold A (z! U) P,hv, inter_empty]
        have hg : inspected P⊆Y:= by
           have hk: halo 8 P⊆ halo (2*M+8) X:= by
             intro i hi; obtain ⟨b,hb,hP⟩:=halo_spec.mp hi; obtain ⟨w,hx,hT⟩:=halo_spec.mp hb; exact halo_spec.mpr ⟨w,hx,(separation_triangle w b i).trans (Nat.add_le_add hT hP)⟩
           exact (Next.Scheduling.flag_layer P).trans (hk.trans q.crest)
        exact agrees_mono hm (coe_subset.mpr hg)
    exact hs
lemma planT (t:IV F (board F X) G) (hU:U∈hotel F X Y J W μ A B)(hx:twirl (G:=G) (S:=S) F (board F X) t U∈hotel F X Y J W μ A B): Place X M (canoe (S:=S) F U) (z! U) (canoe (S:=S) F (twirl (G:=G) (S:=S) F (board F X) t U)) (z! (twirl (G:=G) (S:=S) F (board F X) t U)) R.p.threshold ∧ Place X M (z! U) (z! U) (z! (twirl (G:=G) (S:=S) F (board F X) t U)) (z! (twirl (G:=G) (S:=S) F (board F X) t U)) R.p.threshold:=by
   obtain ⟨a,b⟩:=unfoldR F X Y J W μ g q.extendsX U t
   obtain ⟨-, -, hV, hY,hW⟩:= pose g q hU; obtain ⟨-, -, hV', hY',hW'⟩:=pose g q hx
   refine ⟨⟨a,b,agrees_mono hV (coe_subset.mpr q.gazes),agrees_mono hV' (coe_subset.mpr q.gazes),hW,hW'⟩,b,b,fun _ _ _=>rfl,fun _ _ _=> rfl, ?_,?_⟩
   · unfold Healthy; simp [hY]
   unfold Healthy; rw [hY']; simp
lemma dues (t:IV F (board F X) G) (hU:U∈hotel F X Y J W μ A B)(hx:twirl (G:=G) (S:=S) F (board F X) t U∈hotel F X Y J W μ A B): flags R.p.threshold (twirl (G:=G) (S:=S) F (board F X) t U)=flags R.p.threshold U:=by
    obtain ⟨hs,hz⟩:= planT g q t hU hx; have hp:flags R.p.threshold (canoe (S:=S) F U)=flags R.p.threshold (canoe F (twirl (G:=G) (S:=S) F (board F X) t U)):=by
        ext j; by_cases hi:j∈halo (2*M) X
        · exact iff_of_false (fun he=> disjoint_left.mp hs.seals_old hi he) (fun he=> disjoint_left.mp hs.seals_new hi he)
        have hk: 2 ≤ M:= le_trans (le_trans (b:=deepCopy R.p k) (by unfold deepCopy; nlinarith) le_rfl) q.bank
        exact untouched R.p.threshold j (fun he=>hi (Corona.halo_mono (by omega : 4 ≤ 2*M) subset_rfl he)) hs.old
    unfold canoe at hp; simp_rw [gauge_flags] at hp; exact hp.symm
include h hD
lemma bursts (t:IV F (board F X) G) (hU:U∈hotel F X Y J W μ A B)(hx:twirl (G:=G) (S:=S) F (board F X) t U∈hotel F X Y J W μ A B):
      S.density R.beta U W=S.density R.beta (twirl (G:=G) (S:=S) F (board F X) t U) W*Real.exp (-R.beta*sigh S i W (z! U) (z! (twirl (G:=G) (S:=S) F (board F X) t U))):=by
    have he:∀ D:Config G f,S.density R.beta (canoe (S:=S) F D) W=S.density R.beta D W:=fun D=>by rw [← S.covary hD (F.foldAt D) R.beta D W]; exact congr_arg _ (by funext; simp [Lattice.gauge,F.fold_root])
    have hq:= (planT g q t hU hx).1; rw [← he U,← he (twirl (G:=G) (S:=S) F (board F X) t U)]
    let p₀(v):=meetVar x (rented F Y J W μ v); have hZ (Z:Config G f) : fine G F (p₀ Z)= chambers F Y J W μ Z:=by unfold fine; simp_rw [p₀]; unfold outer; rw [paint_meet]; rfl
    have hV(Z:Config G f):outer G F (p₀ Z)=W:=by unfold outer p₀; rw [paint_meet]
    have hr :0 ≤ B:= q.height; have hp: K<p.initial:=lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg zero_le_two hr)) q.room
    have ht(v:Config G f)(he:v∈hotel F X Y J W μ A B):p₀ v ∈ ball 0 p.initial:=mem_ball.mpr (by rw [dist_zero_right]; exact ((pose g q he).2.1).trans_lt hp)
    apply payday S hD q.solid ⟨hq.old,hq.afterX,hq.source,hq.sinks⟩ W ((hZ U) ▸ h.enrollment (p₀ U) (ht U hU)) ((hZ _) ▸ h.enrollment _ (ht (twirl (G:=G) (S:=S) F (board F X) t U) hx)) i (fun j=> ?_)
    have hc:=h.choice (p₀ U) (ball_subset_ball p.enroll (ht U hU)) j; have hd:= h.choice _ (ball_subset_ball p.enroll (ht (twirl (G:=G) (S:=S) F (board F X) t U) hx)) j
    rw [hV,hZ] at hc hd; rw [hc,hd]
end Posture
end YM.MSbar.Heath.Cottage
