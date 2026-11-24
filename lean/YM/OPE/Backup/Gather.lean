import YM.OPE.Backup.Remedy
import YM.OPE.Sweep.Join
/-!
# Grouping ticket with dormant paths carried

Uses 2 units of exponent of the next step, never pays them again. Per singleton
radii preserved exact through the designated `W`; get another radius facility
for the mixed terms afterwards; can take whichever is smaller. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Muster
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Source
open Extra.Trajectories MergeProof.Float OPE.Backup
open scoped Topology BigOperators Classical
variable {V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}
local notation "X"=> Names V I
local notation "Y"=> Names V J
set_option quotPrecheck false
variable {H:History G}{δ σ θ : ℕ→ℝ}{m N p a:ℕ} {R:ℝ}
local notation "K₀"=> H.rep N p m
local notation "P₀"=> (H.levels.budget m)
local notation "x"=> (P₀).supportExponent
variable {E:V→Motion}{B:V→ Equiv.Perm V}{v:V}{L:Ward (Names V I)}{U:Ward (Names V J)}
    {o:V×I→ Site (H.S.side m p)}{u:V→Site (H.S.side m p)}{F:V×I → Config G (H.S.side m p)→ℂ}{K: V×I→ℕ→ Config G (H.S.side m p)→ℂ}{c:V×I→ℂ}
    (q:Config G (H.S.side m p)→ Poly (Names V I))
variable (h:H.Selected) {D: ∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)} {r:ℕ→ℕ}(ht:Thor H δ r D σ θ a)
    (A:Fibers I J) (s:Finset J){W:I→ℝ} {t l:ℕ}{c':ℝ}
-- remove θ shadow
local notation "A'"=> partialGroup V A
local notation "g"=> (A').twig

lemma expWalk {y:ℝ}(h: 0 ≤ y)(hr:y≤1): Real.exp y-1 ≤ 2*y:=by
    have he: y ≤ Real.log (1+2*y) := by apply le_trans _ (Real.le_log_one_add_of_nonneg (mul_nonneg zero_le_two h)); refine (le_div_iff₀ (by positivity)).2 ?_; nlinarith [mul_le_mul_of_nonneg_right hr h]
    linarith only [Real.exp_log (show 0 < 1+2*y by positivity),Real.exp_monotone he]
lemma spareStake {M:ℕ}{v y C:ℝ}(h:M≥1)(hh:0≤ y)(he:0≤ v)(hd: ((M+M+1:ℕ):ℝ)^4*(v+C)≤1/2) (hc: ((M+M+1:ℕ):ℝ)^4 * y ≤ 1/2) :
     ((M+M+1:ℕ):ℝ)^4 * (Real.exp y-1+C) ≤ 2 ∧ Real.exp (Real.exp y-1+C)-1 ≤ 1:=by
    let hq : 4 ≤ ((M+M+1:ℕ):ℝ)^4:=by calc _ ≤ (↑(3:ℕ):ℝ)^4:=by norm_num
                                           _ ≤ _:=by gcongr; omega
    let B:ℝ:=((M+M+1:ℕ):ℝ)^4; have heQ:4 ≤ B:=hq; have hk:y ≤ 1:= by change B*y≤1/2 at hc; nlinarith only [hc,mul_le_mul_of_nonneg_right heQ hh]
    let z:=Real.exp y-1; have hy:B*(z+C) ≤ 2:=by change B*y≤1/2 at hc; change B*(v+C)≤1/2 at hd; have hp:z≤2*y:=expWalk hh hk; have ht:0≤B:=(by linarith); nlinarith [mul_le_mul_of_nonneg_left hp ht];
    refine ⟨hy,?_⟩; by_cases h:0 ≤ z+C; · have he:z+C≤1/2:=(by linarith only [hy,mul_le_mul_of_nonneg_right heQ h]); have hp:= expWalk h (show z+C ≤ 1 by linarith only [he]); linarith only [he,hp]
    change Real.exp (z+C)-1≤1; linarith only [Real.exp_monotone (le_of_lt (lt_of_not_ge h)),Real.exp_zero]

-- Passing ticket math
include h ht
local notation "Q" => (fun i=> profile (K₀).activities (K i))
local notation "τ" => (fun j:V×J=> grouped H δ t l m W A j.2)
local notation "S"=> (fun U'=> Fibers.reap A' (q U'))
set_option maxHeartbeats 800000 in
lemma buccGather (hs:∀ i∈s,A.Solo i)(hk:a ≤ m)(hn:m<N)
    (hB:Buccaneer K₀ B E v L o u F K q (fun i=>δ m*W i) (δ m) (θ m) c)(hm:May v E u B F (fun i=>profile (K₀).activities (K i)) c)(hp:∀ w,w≠v→∀ i:I,o (w,i)=affine (E w).1 (u w) (o (v,i)))
    (hC:ClusterPars H δ θ r m)(hw:∀ i,0<W i)
    (hV:Arsenal K₀)(hy:0<t)(hQ: Fintype.card I≤ t)
    (ho:Occupancy o (r m))(ho':Occupancy (o ∘ g) (r m))
    (hR:∀ i:V×I,δ m*W i.2*‖c i‖ ≤ 1)
    (hS:∀ i:V×I, coverNumber (P₀).B ({(o ∘ g) (A'|>.bunch i),o i}:Support _ ) ≤ l)
    (h_Y:∀ i:(Y).Mode,U.ready i→L.ready (A'|>.plena i)) : -- typo pipe
    ∃ (F':V× J→ Config G (H.S.side m p) →ℂ) (K': V×J →ℕ→ Config G (H.S.side m p)→ℂ), let Q':=fun i=>profile (K₀).activities (K' i)
      Bard K₀ U v E B u (o ∘ g) F' Q' S τ (x-2) ∧ May v E u B F' Q' (fun _=>0) ∧ (∀ i,Dominated (K' i)) ∧
        (∀ i:V×J,i.snd∉s → Blade K₀ (o (g i)) (F' i) (Q' i) 0 (4*(1/τ i))) ∧ ∀ i:V×J,i.snd∈s → F' i=F (g i) ∧ K' i=K (g i):=by
    let P:=K₀; have hA:= h.represents N p m hn.le; have hxP:P.p=P₀:=hA.vac; obtain ⟨q',hX,hφ⟩:= hB.move; obtain ⟨p0,q0,ψ,hψ,hE,hF,hK,hp0,hq0,hH,hω,hV',hI⟩:= hX.see
    let w(i:V×I):=δ m*W i.snd; let f':= Fibers.reap (A'); let C (i:V×I):= if A.bunch i.2 ∈ s then 0 else c i
    let Λ:Fibers.Salt (V×J) (V×I) (A') G (H.S.side m p) := ⟨o,C,p0,q0⟩
    let y:= (P.p).supportExponent+1/2; have hu := ht.suns m hk; have hz:0 < δ m:= hu.hats.1; have hb: δ m ≤ 1:= hu.hats.2; have ht(i):0<w i:= mul_pos hz (hw _)
    have hsP :0 ≤ θ m:=by obtain ⟨u0,-,he,-⟩:=hK; exact (tsum_nonneg ((he 0).1)).trans (he 0).2.2
    have hx: Λ.Breeze P.p.threshold :=⟨hp0,hq0⟩
    have hv(i:V×I) : w i*‖Λ.pepper i‖≤ 1:=by change _*‖C i‖≤_; unfold C; split; simp; exact hR i
    let x':=τ; let α:=Ribbons.Salt.scent P.p.B (r m) y 1 (δ m) 1 (θ m); let α':= Real.exp α -1
    have hX(k:V×J):0<x' k:= Finset.prod_pos fun i _=>mul_pos (license_pos _ _ hz hy) (hw _)
    have hK': Towed w Prod.fst q0 P.p.B y (θ m):=hK.shrink (by unfold y P; linarith only) le_rfl ht
    have hLambda (i:V×I): coverNumber P.p.B ({Λ.focus (A'|>.bunch i),Λ.grain i}:Support _) ≤ l:=by rw [hxP]; exact hS i
    have he' : 0≤ α:=by unfold α Ribbons.Salt.scent; positivity
    let W':= Fibers.Salt.tow w y (δ m/t) l
    have h_X(i:V×J): x' i=∏ j ∈ (A').contents i, W' j:=by
       unfold W' y; rw [hxP]; exact grouped_b t l A i
    have hQ' := cardinal_le (V:=V) _ A hQ
    have hg:= P.p.B_pos; have h_A: ((P.p.B+P.p.B+1:ℕ):ℝ)^4*α ≤1/2:=by unfold α y; rw [hxP]; exact hC.bars.1
    have h_A':α' ≤ 1:= by unfold α' α y; rw [hxP]; exact hC.bars.2
    obtain ⟨k₀,hk₀⟩:= Λ.materialize (w:=x') (J:=w) (r m) l (δ m) 1 1 t hy hV hx hA.good.labels hω ht ho zero_le_one hv hg hz hb hLambda (by norm_num : (0:ℝ) ≤ 1/2) hF hK' hQ' (fun U=>(Tour.bright H h N p m hn.le U).ne') h_X h_A h_A'
    have Hq:= Λ.rate w P.p.threshold y 1 (δ m) (r m) P.p.B l ht ho hv hg hz hb hLambda t hy hQ' 1 (θ m) zero_le_one hF hK' (add_nonneg (P.p).exponent_pos.le (by norm_num))
    obtain ⟨hQ₀,hX₀⟩:= (Λ.vessel P.p.threshold).carries _ (Λ.wet _ hx) W' x' _ (1/2) _ P.p.B Hq P.p.exponent_pos.le (fun i=> Fibers.Salt.towP w y (δ m/t) _ ht (by positivity) _) h_X h_A
    have hx(i:V×J)(hs_:i∈crew V s): x' i ≤ w (g i):=by
       unfold w; rw [h_X,(crewed _ s hs i hs_).content,prod_singleton]; unfold W' Fibers.Salt.tow; have h': 1 ≤ (t:ℝ):=by exact_mod_cast hy
       refine (div_le_self (mul_nonneg (by positivity) (ht _).le) (Real.one_le_exp (mul_nonneg (by unfold y; exact add_nonneg P.p.exponent_pos.le (by norm_num)) (Nat.cast_nonneg _)))).trans ?_; exact mul_le_of_le_one_left (ht _|>.le) ((div_le_self hz.le h').trans hb)
    obtain ⟨hV,hW,hF',hC⟩:= lodging (C:=c) (q:=q') (hr:=fun i=> (show Λ.pepper i= _ from rfl)) hs ‹Λ.Breeze P.p.threshold› rfl hI hH (F:=k₀) (fun j hj k=>⟨hp j hj k,(hm j hj|>.2 k).2.2⟩) hk₀ (hQ₀.shrink le_rfl h_A' hX) hX₀ hω hm hψ hE hV' (fun i U=> hB.coinPart hφ i U) hB.liq hx hz.le (fun i=> (hX i).le) hA.good.labels
    let f'(i:V×J):= if i.snd∈s then F (g i) else Λ.debt P.p.threshold i; let Fk(i:V×J):= if i.snd∈s then K (g i) else k₀ i; let Q'(i:V×J):= profile P.activities (Fk i); let Vq:=fun U=> Fibers.reap A' (q' U)
    have he:=hu.stakes.1; rw [← hxP] at he
    obtain ⟨hy',hy₀⟩:= spareStake hg he' hsP he h_A
    have hS_ : Arc P f' Fk Vq v E u B (o∘g) τ (x-2+2) x 1 α' (δ m) (gyro c A s):=by rw [show x-2+2=x from sub_add_cancel ..,← hxP]; exact hV
    have H' : Serves P f' Q' Vq v E u B (o∘g) τ (x-2) 1:=by -- can consume extra 2 here with μ=? thru u=x-2 ζ=2 requires Repeg ζ=2 vac, e minus (u+ζ)=0 insufficient. lower Arc regular exponent allowed. need Arc.weaken or set thru t=x-2,ζ=0 Arc of exponent x-2.
       obtain ⟨a0,K',p',ha,hh,hV',u0,hS',H_⟩:=hV.see -- hV is ???
       apply thru (Z:=1) (ζ:=0) (u:=x-2) (?_:Arc P f' Fk Vq v E u B (o∘g) τ (x-2+0) P.p.supportExponent 1 α' (δ m) (gyro c A s)) hA.good.labels hX hz.le ho' (by linarith only [hu.exp.1]) ?_ hX (by simp [Repegs,x']) zero_le_one (by norm_num) (by rw [one_mul]; exact hy₀) hC hF' (fun U=>(Tour.bright H h N _ m hn.le U).ne')
       · exact ⟨a0,K',p',ha,hh,hV'.shrink (by change _ ≤ P.p.supportExponent; rw [hxP]; linarith only) le_rfl hX,u0,hS',H_⟩
       exact hy'.trans_eq (by rw [hxP]; ring)
    refine ⟨f',Fk,⟨⟨Vq,H', fun U_ i hi=> hφ U_ _ (h_Y i hi)⟩⟩, fun j hj=>?_,hF',fun i hi=>?_,fun i hi=>?_⟩
    · exact ⟨(hW j hj).1, fun v=>⟨(hW j hj|>.2 v).1,(hW j hj|>.2 v).2.1, (scalar_z _).symm⟩⟩
    · unfold f' Fk; dsimp only; rw [if_neg hi,if_neg hi]; exact (hk₀.foot i).2
    exact ⟨if_pos hi,if_pos hi⟩
end YM.MergeProof.Ribbons.ManyCopies.Muster
