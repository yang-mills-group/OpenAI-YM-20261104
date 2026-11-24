import YM.OPE.Compatible.Assemblage.Runs
/-!
# Off-grid approach before a localized purchase

Single slot at any offset sees a rough L^4 cost per step. Use only on the
short approach segments scheduled *after* individual preparations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G : Gauge}{A:History G}{V :Type} [Fintype V][DecidableEq V]{N p m j k:ℕ}
variable (P:Ensemble V) {D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
namespace Run
def Below (A:History G)(w:ℝ)(j m:ℕ):ℝ:= w*(A.S.a j/A.S.a m)^4
variable {P} {w xx:ℝ}{E:Track A V p}
lemma below_fee (A:History G)(hw:0<w): 0< Below A w j m:=mul_pos hw (pow_pos (div_pos (A.S.a_pos _) (A.S.a_pos _)) _)
lemma below_scale (A:History G) : Below A w j (m+1)= ((A.S.block m).val:ℝ)^4 * Below A w j m:=by
   unfold Below; have he := A.S.block_large m
   rw [A.S.a_step]; have hh: (0:ℝ)< (A.S.block m).val :=by positivity
   have hz:= A.S.a_pos m; field_simp
lemma below_main (A:History G):Below A w m m=w:=by unfold Below; rw [div_self (A.S.a_pos _).ne',one_pow,mul_one]
variable (hA:A.Selected)(hn:m<N) {Z : Stem V G (A.S.side (m+1) p)} {v w₀ t :ℝ} {x:ℂ}
local notation "d"=>A.rep N p (m+1)
local notation "u"=>A.rep N p m
local notation "L"=> A.S.block m
local notation "Q"=> A.levels.clock.op m p
include hA hn
lemma advance (E:V→Site (A.S.side m p))(hs: Marked (A.rep N p (m+1)) (fun i=>(A.levels.clock.op m p).ratio.embed (E i)) P Z)
    (hp : Blade d (Z.home P.v) (Z.oil P.v) (profile (d).activities (Z.gas P.v)) x t)
    (hr:MergeProof.Float.Runs (D N p m hn) Q xx)(hi:0≤xx)(hw:2*w₀*t≤1)(hξ:w₀ * ‖x‖ ≤ 1):
    ∃ Z':Stem V G (A.S.side m p), Marked u E P Z' ∧ Journey (D N p m hn) Q P Z Z' w₀ x ∧ Blade u (Z'.home P.v) (Z'.oil P.v) (profile (u).activities (Z'.gas P.v)) x (xx*t):=by
    have he:= hA.represents N p (m+1) hn; have he':= hA.represents N p m hn.le
    obtain ⟨f,k,hh,hK,hP,hM⟩:=Float.slosh hp he.good (hs.spends _) hr hi he'.good.labels (hA.steps N p m hn|>.1.symm) (A.levels.transition_mass m p _)
    let o':= (A.levels.clock.op m p).ratio.parent ∘ Z.home
    have hh'(j:V)(hx:j≠P.v): o' j=affine (P.move j).1 (E j) (o' P.v):=by unfold o';rw [comp_apply,hs.sym j hx]; exact Push.Local.parent_affine _ (A.S.block_odd _) _ _ _
    obtain ⟨U,hU,hf,hk,hT⟩:= submit hA hn.le f (P:=P) hK o' hh'
    obtain ⟨S,hS,h⟩:=hP
    refine ⟨U,hU,⟨hT.symm, promoted hA hn (by assumption) (Float.spill_in hp he.good ?_) hU ?_, ⟨S,hS,t,0,hw,by simp,?_⟩, hξ⟩,?_⟩
    · exact hs.spends _
    · unfold Stem.sub; rw [hf,hk]; exact hM.symm
    · rw [hk,hT]; exact h
    rw [hf,hk,hT]; exact hh
omit hn
variable {X:Stem V G (A.S.side j p)}
set_option maxHeartbeats 200000 in
lemma descenders (hk:k ≤ j)(hN:j≤N)(hm:Migrating A k p j E)(h:Marked (A.rep N p j) (E j) P X)(hL: ∀ i:ℕ,k ≤ i→∀ hi:i < j,MergeProof.Float.Runs (D N p i (hi.trans_le hN)) (A.levels.clock.op i p) (6*((A.S.block i).val:ℝ)))
    (hf: Blade (A.rep N p j) (X.home P.v) (X.oil P.v) (profile (A.rep N p j).activities (X.gas P.v)) x (1/(2*w)))
    (hω:w*‖x‖≤1)(hw:0<w)(o:Track A V p)(hW:o j=X.home)(hp:∀ i,k ≤ i → i<j → (A.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i):
    ∃ Z:Travel A V p, Z j=X ∧ Run P D N p k j E o Z (Below A w j) ∧ Blade (A.rep N p k) ((Z k).home P.v) ((Z k).oil P.v) (profile (A.rep N p k).activities ((Z k).gas P.v)) x (1/(2*Below A w j k)) ∧ Below A w j k*‖x‖≤1:=by -- define strengthened
    let v:= Below A w j; let z:Travel A V p:= fun i=> {home:=o i, oil:=0,gas:=0}; let Z:= update z j X; have he: Z j=X:= update_self j X z
    -- stronger result at every partial k.
    suffices hp' : ∀ b:ℕ,k ≤ b → b≤j → ∃ Z:Travel A V p,Z j=X ∧ Run P D N p b j E o Z v ∧
         Blade (A.rep N p b) ((Z b).home P.v) ((Z b).oil P.v) (profile (A.rep N p b).activities ((Z b).gas P.v)) x (1/(2*v b)) ∧ v b* ‖x‖≤1 by exact hp' k le_rfl hk
    intro b hK hb
    induction hb using Nat.decreasingInduction with
    | self=>
       have hv:v j=w:=below_main _; refine ⟨Z,he,baseRun hN (hv.symm ▸ hw) (he.symm ▸ h) (by rw [he,hW]),?_,hv.symm ▸ hω⟩; rw [hv,he]; exact hf
    | of_succ i hi ih=>
       obtain ⟨Z,hX,hG,he,hU⟩:= ih (hK.trans i.le_succ)
       let Z':= Z (i+1); have hq : Marked (A.rep N p (i+1)) ((A.levels.clock.op i p).ratio.embed ∘ E i) P (Z (i+1)):= (hm.mare i hK hi).symm ▸ hG.marks _ le_rfl hi
       have hu: 0 < v i := below_fee (m:=i) (j:=j) A hw; have hu':0 < v (i+1):= below_fee (m:=i+1) (j:=j) A hw
       let S:ℝ:=(A.S.block i).val; have hx : (2:ℝ)≤ S:= by unfold S; exact_mod_cast (show 2 ≤ (A.S.block i).val from (show 2 ≤ 3 from by decide)|>.trans (A.S.block_large i))
       have hv:v (i+1)= S^4*v i:=below_scale A
       obtain ⟨Y,hpY,hY,hqY⟩:= advance hA (hi.trans_le hN) (E i) hq he (hL _ hK hi) (by change (0:ℝ) ≤ 6*S; linarith only [hx]) (w₀:=v (i+1)) (by
          have he:=show 2*v (i+1)≠0 from (mul_pos (by norm_num) hu').ne'; rw [mul_one_div, div_self he]) hU
       let f':Travel A V p:= update Z i Y; have hh : f' i=Y:= update_self ..; have hE j (he:i<j) : f' j=Z j:=update_of_ne he.ne' ..
       have huY:Y.home=o i:= hY.site.symm.trans ((congr_arg _ (hG.steers _ le_rfl hi)).trans (hp i hK hi))
       refine ⟨f',(hE _ hi).trans hX,Run.together (j:=i+1) ?_ (hG.shift (fun k hk _=>⟨(hE _ hk).symm,rfl,rfl⟩)),hh.symm ▸ hqY.more ?_,?_⟩ -- argument name
       · refine ⟨Nat.le_succ _, hi.trans_le hN,fun m _ _=> below_fee A hw,fun m ht hr=> ?_,fun m ht hr=>?_,fun i' he hT=>?_⟩
         · rcases eq_or_ne i m with rfl|hx; exact hh.symm ▸ hpY
           exact (hE m (by omega)).symm ▸ hG.marks m (by omega) (hr.trans hi)
         · rcases eq_or_ne i m with rfl|hx; rw [hh,huY]
           rw [hE m (by omega)]; exact hG.steers m (by omega) (hr.trans hi)
         obtain rfl:i'=i:= by omega
         rw [hh,hE _ i'.lt_succ_self]; exact ⟨_,hY⟩
       · change 6*S*(1/(2*v (i+1)))≤1/(2*v i)
         rw [← mul_div_assoc,mul_one,hv]; apply (div_le_div_iff₀ (mul_pos two_pos (hv ▸ hu')) (mul_pos two_pos hu)).2
         have hg:=pow_le_pow_left₀ zero_le_two hx 3; rw [one_mul,mul_comm _ (_ * _)] -- adjust
         nlinarith -- nonlinear
       exact (mul_le_mul_of_nonneg_right (hv.symm ▸ (le_mul_of_one_le_left hu.le (one_le_pow₀ (one_le_two.trans hx)))) (norm_nonneg _)).trans hU
end Run
end YM.MergeProof.Ribbons.ManyCopies.Stem
