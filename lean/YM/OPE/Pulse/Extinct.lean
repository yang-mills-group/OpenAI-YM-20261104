import YM.OPE.Pulse.Drive
import YM.OPE.Loom.Ticket
/-!
# Staying alive for arbitrary separation of branch levels
Propagate a weight-zero Club to coarse without putting a fresh field in.
`e0` has constant (real complexified)-leg budget along the history, **with
zero separate Music charge**. The (unreturned) Woke direction contracts, giving total
paid once. Aligned center over arbitrary branch with path at fixed radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Relay Bid
open Extra.Trajectories MergeProof.Float Next.Rank Edition Spindle Extra.Multi
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{d:ℕ} {H:History G} {C:Family G}
open Labels
lemma solo_basis (F: Frame G 0) (v:F.Coeff) : ∃ y:ℂ,v=y • F.e0:=by
   obtain ⟨x,rfl⟩:= F.coords.surjective v; have hx:= decompose x
   obtain ⟨u,hU⟩:= scalar_grade _ (gradePart_mem (0,0) x); simp only [Nat.zero_add] at hx; simp only [range_one,sum_singleton] at hx
   exact ⟨u,by rw [hx] at hU; rw [hU,map_smul,F.coords_unit]⟩
variable {N p k i j:ℕ} {W : Bid.Worth} {u ψ φ δ:ℕ→ℝ} {ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "Y" => C.path
local notation "F" => C.labels.level 0
local notation "L" => C.localSection 0
local notation "τ" => C.params
local notation "R" => C.path.rep N p
variable {M:Extra.Histories.Music (C.labels.level 0) C.path N p}
lemma plain_wind (h:Heard L Y N p C.params i (M.tone i))(x:C.label 0): (M.tone i).index x=x ∧ (M.tone i).charge x=0:=by
    have ht:= h.unit; simp only [Source.unitVec,pow_zero,one_smul] at ht
    obtain ⟨y,hY⟩:= solo_basis F x; have he : (M.tone i).index x=x:= by rw [hY,map_smul,ht]
    refine ⟨he,?_⟩
    apply le_antisymm (le_trans (h.cone x) (le_of_eq ?_)) (rem_nonneg (h.earns x).2)
    rw [he,hY,map_smul, Size.unit_core]; simp [Frame.coeffSize]
variable {P:Coefficient (C.labels.level 0) (C.S.side k p)} {w a:ℝ} (o:∀ i,Site (C.side i p)) (X:Lamp G (C.side k p)) (h:C.Makes)(hr:Scrim C W u ψ φ δ ζ r D)
include h hr
-- may be hoisted outside arbitrary projection arguments. assumes moment price at capture.
lemma pure_wind (hk:k ≤ N)(hi:i ≤ k) (hx:C.ref 0 ≤ i)(hf:P.Format 0 C.params (R k))(hb:P.remBound 0 (R k) (kappa C.path k) a)
   (he:(F).coeffSize P.x≤ a)(hw:0<w)(hC:∀ j:ℕ,i ≤ j→ j≤k → w * (32*(1+(C.path.levels.params k).columns)*a) ≤ ζ 0 j):
    ∃ (Z:∀ i:ℕ,Coefficient (C.labels.level 0) (C.S.side i p)) (t:ℕ→ℝ), Club (Y) C.params (L) (ζ 0) ψ i k N p (fun _=>w) D Z t hk ∧
      (Z k).exponentialEntry 0 L (R k)=P.exponentialEntry 0 L (R k) ∧ profile (R k|>.activities) (Z k).forced= profile (R k|>.activities) P.forced:=by
    obtain ⟨M,hM,hL,hΨ,hϕ⟩:= (hr.costs.aim 0 N p (hx.trans (hi.trans hk))).lyrics; obtain ⟨A,hA,ha,hX,hU,hY,hβ,hε⟩:= antilles L Y N p C.params W M (D N p) ψ hx hi hk h.wilson hL (fun j hj hj' => ⟨hr.listens _ _ _ _ (hx.trans hj) (hj'.trans_le hk),hΨ j (hx.trans hj) (hj'.trans_le hk)⟩) P hf hb (show (F).coeffSize P.x + a ≤ 2*a from by linarith only [he]) hr.costs.cost hr.costs.back
    let x:= -(A i).a; let Z':= dualize Y N p M i k A x; let Z:= dualize Y N p M i k A 0; let y:=(C.path.levels.params k).columns; let E:= 4*(1+y)*(2*a)
    have ht:0 ≤ a:= rem_nonneg hb; have hE:0≤E:=by have he:1 ≤ y:= (C.path.levels.params k).columns_ge; unfold E; positivity
    have hL' (j) (hq:i ≤ j) (hr:j ≤ k) := (hL.earned j (hx.trans hq) (hr.trans hk))
    have hΩ(j)(hm:i ≤ j)(hn:j ≤ k)(x):= keys L Y N p C.params M x (ha.chairs _ hm hn) (hL' _ hm hn)
    have hz(j)(hm:i ≤ j)(hn:j ≤ k) : Z'.cost j+(F).coeffSize (Z'.voice j).x≤ E:=by
       apply le_trans _ (hε j hm hn)
       have ht : 1 ≤ gainChart Y k j:= Real.one_le_exp (mul_nonneg (by norm_num) (sub_nonneg.mpr ((YM.OPE.scale_mono C.S).monotone hn))) -- location
       exact le_mul_of_one_le_left (add_nonneg (rem_nonneg (hΩ _ hm hn x|>.2.2)) (Work.G08.size_nonneg ..)) ht
    have hv(j)(he:i ≤ j)(ht:j≤k)(b) : ((A j).bar M b).x=(A j).a+b:= (hΩ _ he ht b).1.trans (plain_wind (hL' _ he ht) _|>.1)
    have hg: (Z.voice k).x=P.x:= (hU 0).1.trans (by rw [map_zero, add_zero]); have hw': (Z'.voice k).x=P.x+x:= (hU x).1.trans (by rw [(plain_wind (hL' _ hi le_rfl) _).1])
    have hp : (F).coeffSize (-x) ≤ a+E:= by
       apply le_trans _ (add_le_add he (le_trans (le_add_of_nonneg_left (rem_nonneg ((hΩ k hi le_rfl x).2.2))) (hz k hi le_rfl)))
       rw [show -x=P.x + - (Z'.voice k).x from by rw [hw']; abel]; apply (Size.add ..).trans; simp [Frame.coeffSize]
    refine ⟨Z.voice,Z.cost,⟨fun j hm hj=> (hΩ _ hm hj _).2,?_,?_⟩,?_,?_⟩
    · intro j hj he; have hx:(Z.voice j).x = (Z'.voice j).x + -x:= by change ((A j).bar M _).x=((A j).bar M _).x+_; rw [hv _ hj he,hv _ hj he]; abel
      have hr:Z.cost j=Z'.cost j:= by unfold Z Z' dualize Solo.cost; dsimp only; rw [(plain_wind (hL' _ hj he) _).2, (plain_wind (hL' _ hj he) _).2]
      rw [alto_norm,pow_zero, inv_one, mul_one]; apply le_trans _ (hC j hj he); apply mul_le_mul_of_nonneg_left _ hw.le; apply le_trans (add_le_add (le_of_eq hr) (hx ▸ Size.add F (Z'.voice j).x (-x)))
      have hv:= hz _ hj he; have hY :1≤y:= (C.path.levels.params k).columns_ge; unfold E at *; change _ ≤ 32*(1+y)*a; linarith only [ht,hv,hp,mul_nonneg (sub_nonneg.mpr hY) ht] -- nonlinear * order grouping
    · intro j hj he; obtain ⟨t,ht,hP⟩:= (hX j hj he).plays; exact ⟨(ha.ships _ hj he).debt _,t,ht,hP _⟩
    · let I:=M.tone k; let y:= I.index.symm P.x; let V:= fun x=> (I.plays x).exponentialEntry 0 L (R k); have hy':=hL' _ hi le_rfl; have hz(b):=(hy'.earns b).2; have hQ : (V (-y)) = -V y:= (IsLinearMap.mk' _ (expoLinear I.plays I.charge hy'.book hz)).map_neg y
      unfold Z dualize; dsimp only; rw [hA]; unfold Solo.bar pair; simp only [add_zero]; let P':=beside P (I.plays (-y)); change (beside P' (I.plays y)).exponentialEntry 0 L (R k)=_; rw [duo_exp L ((presentation hf hb (hy'.earns (-y)).1 (hz (-y))).2) (hz y), show P'.exponentialEntry 0 L (R k) = _ from duo_exp L hb (hz (-y))]; change _+V (-y)+V y=_; rw [hQ]; abel
    let I:=M.tone k; let y:= I.index.symm P.x; let V:= fun x=> profile (R k|>.activities) (I.plays x).forced; have hy':=hL' _ hi le_rfl; have hz(b):=(hy'.earns b).2; have hQ : V (-y)= -V y:= (IsLinearMap.mk' _ (inkL I.plays I.charge hy'.book hz)).map_neg y
    unfold Z dualize; dsimp only; rw [hA]; unfold Solo.bar pair; simp only [add_zero]; let P':=beside P (I.plays (-y)); change profile (R k|>.activities) (beside P' (I.plays y)).forced=_; rw [duo_profile ((presentation hf hb (hy'.earns (-y)).1 (hz (-y))).2) (hz y), show profile (R k|>.activities) P'.forced = _ from duo_profile hb (hz (-y))]; change _+V (-y)+V y=_; rw [hQ]; abel
include X
lemma lantern (hk:k ≤ N)(hi:i ≤ k)(hx:C.ref 0 ≤ i)(hI:Ignite Y N p k C.params (L) P a (o k) X)(hw:0<w)(hC:∀ j:ℕ,i ≤ j→ j≤k → w * (32*(1+(C.path.levels.params k).columns)*a) ≤ ζ 0 j)
   (ho:∀ j,i ≤ j→ j<k→ o (j+1)=(C.path.levels.clock.op j p).ratio.embed (o j)) : ∃ S, S k=X ∧ Drive C.path i k N p o (fun _=>w) D S hk:=by
   obtain ⟨Z,t,hZ,hα,hβ⟩:= pure_wind h hr hk hi hx hI.fuel hI.power.1 hI.power.2 hw hC
   obtain ⟨S,hS,hA⟩:= beam Y C.params L (ζ 0) ψ i k N p (1,false) o (fun _=>w) D Z t h.wilson (h.sections 0) hk hZ (fun _ _ _=>hw) (fun _ _ _=>le_rfl) ((hr.costs.heights 0 i N p hx (hi.trans hk)).choose_spec.1) ho (fun i _ hm=> by obtain ⟨_,_,h,-⟩:=hr.costs.night.days N p i (hm.trans_le hk); exact h.propagate)
   let S':= Function.update S k X; have hz(j:ℕ)(he:i ≤ j)(ht:j ≤ k): (S j).watch=(S' j).watch ∧ (S j).rays (R j)=(S' j).rays (R j):=by
      rcases lt_or_eq_of_le ht with ht|rfl; rw [show S' j=S j from Function.update_of_ne ht.ne ..]; exact ⟨rfl,rfl⟩
      rw [show S' j=X from Function.update_self .., hI.track,hI.rays]; obtain ⟨he,hb,hc⟩:= hA j he le_rfl; rw [he,hb]; unfold liftF liftK; rw [hα]; unfold sunny; rw [hβ]; exact ⟨rfl,rfl⟩
   refine ⟨S',Function.update_self ..,⟨fun j hj hk'=>?_⟩⟩
   exact Debt.remap (hS.drives j hj hk') h.wilson (hk'.trans_le hk) (hz (j+1) (hj.trans j.le_succ) hk').1 (hz j hj hk'.le).1 (hz (j+1) (hj.trans j.le_succ) hk').2 (hz j hj hk'.le).2
end YM.MergeProof.Ribbons.ManyCopies.Patrol
