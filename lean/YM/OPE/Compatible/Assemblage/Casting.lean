import YM.OPE.Compatible.Assemblage.Charges
import YM.MergeProof.North.Elders
/-!
# Cast a merged branch at any aligned pivot, then move it as that
primary. This is still NOT selecting the canonical match.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge} {A:History G}{N p m d:ℕ}{V:Type} [Fintype V][DecidableEq V]{P:Ensemble V}{E:V→Site (A.S.side m p)}
variable {D:GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}{z:V→ Site (A.S.side m p)}
variable {w t a:ℝ}{W:Stem V G (A.S.side (m+1) p)}
set_option quotPrecheck false
local notation "X0"=>A.rep N p m
local notation "X1"=>A.rep N p (m+1)
local notation "μ"=> A.levels.clock.op m p
local notation "B"=> Next.Foundations.localSection G d
local notation "F"=> (Labels.frames G).level d
local notation "Y"=> Next.Foundations.hol G
local notation "L" => ((A.S.block m).val:ℂ)^d
omit [Fintype V][DecidableEq V] in
lemma dislodged (h:A.Selected)(he:m<N)(hQ:Marked (A.rep N p (m+1)) (fun i=>(A.levels.clock.op m p).ratio.embed (E i)) P W) (hb:Blade X1 (W.home P.v) (W.oil P.v) (profile (X1).activities (W.gas P.v)) 0 a) {x₀:Site (A.S.side (m+1) p)}(hx:x₀=W.home P.v):∃ l k,Blade (X1) 0 l (profile (X1).activities k) 0 a ∧ Dominated k∧ W.oil P.v=stepUp (1,false) x₀ l∧ profile (X1).activities (W.gas P.v)=floatUp (1,false) x₀ (profile (X1).activities k) ∧ W.sub X1 P.v= stepUp (1,false) x₀ (coin X1 l k):=by
    let x:=x₀; let π:= ((h.represents N p (m+1) he).good.labels.moves 1 (-x)).some
    let hv:= W.oil P.v; let f:= stepUp (1,false) (-x) hv; let S:=profile (X1).activities (W.gas P.v); let g:=floatUp (1,false) (-x) S
    have hk:Blade (X1) 0 f g 0 a:=by
       have ht:= bearer (1,false) (-x) _ _ π (hx.symm ▸ hb); rw [show affine (1:Signed) (-x) x₀=0 from by unfold x;simp [affine]] at ht; exact ht -- dependent rewrite hx issue
    obtain ⟨k,hK,hT⟩:= socket hk; have ht: floatUp (1,false) x (profile (X1).activities k)=S:= hT.symm ▸ reverse_K x _
    refine ⟨f,k,hT.symm ▸ hk,hK,(reverse_F x hv).symm,ht.symm,?_⟩
    exact Eq.trans (congr_arg (fun X=> coin X1 X (W.gas P.v)) (reverse_F x hv).symm) (opals (1,false) A h he x f ((h.represents N p (m+1) he).good.labels.moves 1 x).some hK (hQ.spends _) ht.symm)
lemma edition_leg (h:A.Selected)(he:m<N)(hp:Throws A N p m D Y B t)(hs:SoundDoor (A.levels.clock.op m p) D)
    (hQ: Marked (A.rep N p (m+1)) (fun i=>(A.levels.clock.op m p).ratio.embed (E i)) P W) (hb:Blade X1 (W.home P.v) (W.oil P.v) (profile (X1).activities (W.gas P.v)) 0 a) (hT: (μ).ratio.embed ∘ z=W.home)
    (hA:0 ≤ a)(ht:1 ≤ t)(hw:0<w)(hC:2*w*(2*a) ≤ 1)(hz:w*(t*a) ≤ 1) :
    let c:= A.S.a (m+1)^d*(t*a)
    ∃ y:Coefficient F (A.S.side m p),(F).coeffSize y.x ≤ c∧ y.Format 0 Y X0 ∧ y.remBound 0 (X0) (kappa A m) c∧ ∃ X: Stem V G (A.S.side m p), X.home=z∧ Stamp (N:=N) P B E y X∧ Journey D (μ) P W X w 0:=by
    intro c; let T':= X1; let A':= X0; let b:= z P.v; let y₀:= (μ).ratio.embed b
    have hA0:= h.represents N p (m+1) he; have hA1:= h.represents N p m he.le
    obtain ⟨f,g,hG,hg,hF,hZ,hY⟩:= dislodged (x₀:=y₀) h he hQ hb (congr_fun hT P.v)
    obtain ⟨s,hS,y,h',hp⟩:= tossing A B Y hG hg h he (zero_lt_one.trans_le ht|>.le) hs hp
    let C:= alto A m d; let C':=alto A (m+1) d; let X:= Extra.Histories.stretch C'⁻¹ y
    have hU:‖C'⁻¹‖= A.S.a (m+1)^d:=by unfold C'; rw [norm_inv,alto_norm,inv_inv];
    have hr: X.Format 0 Y X0:= Extra.Histories.stretch_format _ h'.format; have hv:X.remBound 0 (A.rep N p m) (kappa A m) c:= by unfold c; rw [← hU]; exact (Extra.Histories.stretch_rem C'⁻¹ h'.bound)
    have hw_(y): (μ).ratio.parent (W.home y) = z y:=by rw [← hT]; exact (μ).ratio.embed_parent _
    -- name distinguish from hw prior
    have hΔ j(jh:j≠P.v): z j=affine (P.move j).1 (E j) b:=by rw [← hw_ j, hQ.sym j jh]; refine (Push.Local.parent_affine _ (A.S.block_odd _) _ _ _).trans (congr_arg _ (hw_ _))
    obtain ⟨Z,hZ',hy⟩:= realize P B z h he.le hΔ hr hv (Next.Foundations.sound G d)
    have hn:C'⁻¹*C=(L)⁻¹:=by
       rw [show C'=L*C from alto_at ..,mul_inv_rev]; have he:C≠0:= inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (A.S.a_pos _).ne')); rw [mul_right_comm, inv_mul_cancel₀ he,one_mul]
    refine ⟨X,?_,hr,hv,Z,hy,hZ',funext (fun i=>?_), ?_,?_,by simp⟩
    · have ht:= h'.leadP; rw [sub_zero] at ht; refine (?_ : (F).coeffSize X.x ≤ ‖C'⁻¹‖*(t*a)).trans_eq (hU ▸ rfl)
      change (F).coeffSize (C'⁻¹ • y.x) ≤ _; rw [Size.smul]; exact mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left (Work.G08.size_nonneg ..) (orbitCost_one_le ..)).trans ht) (norm_nonneg _)
    · exact (hw_ i).trans (congr_fun hy i).symm

    · apply promoted h he hQ (Float.spill_in hb hA0.good (hQ.spends _)) hZ'.homes
      rw [hY]; change Z.sub A' P.v= (μ).push (X1).beta _; rw [Stamp.equals_gauge B hZ' h he.le (Next.Foundations.sound G d) hr hv,P.spring,hy]
      have hh:= starship A (1,false) b ((L)⁻¹) (coin T' f g) d h'.agrees (Float.spill_in hG hA0.good hg) 1 (show (1:ℂ)= _ from (mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (A.S.block m).property.ne'))).symm); simp only [radiant,one_smul] at hh; rw [← hh]
      rw [show X.density 0 B X0=C'⁻¹ • (y.density 0 B X0) from funext fun U=> Extra.Histories.stretch_density ..]; unfold radiant; rw [scale_F,smul_smul]; exact congr_arg (· • _) ((mul_comm C _).trans hn) -- scope hn above after bullets?
    obtain ⟨π⟩:= hA0.good.labels.moves 1 y₀
    have hp':= hp.gain hs (1,false) b π (show Motion.scalar (1,false) (L) = _ from rfl) |>.pitch 1 ((L)⁻¹) (show (1:ℂ)= _ from (mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (A.S.block m).property.ne'))).symm)
    refine ⟨_,hS.image (Wing.labelRoute π),2*a,‖(L)⁻¹‖*(t*a),hC,?_,?_⟩
    · have hx:1 ≤ ‖L‖:=by rw [norm_pow,Complex.norm_natCast]; exact one_le_pow₀ (by exact_mod_cast (A.S.block m).property)
      have h:‖(L)⁻¹‖ ≤ 1:= by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx
      exact le_trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg (zero_le_one.trans ht) hA) h) (by positivity)) hz -- hw shadow
    have hx:profile (A.rep N p m).activities X.forced= C'⁻¹ • profile (A.rep N p m).activities y.forced:= profile_scale ..
    have hX: profile (A.rep N p m).activities (Z.gas P.v)= (L)⁻¹ • floatUp (1,false) b (profile (A.rep N p m).activities y.forced):=by
       rw [hZ'.price,hy]; unfold sunny; rw [hx,scale_K,smul_smul]; exact congr_arg (· • _) ((mul_comm _ _).trans hn)
    rw [hF,hZ,hX,← congr_fun hT P.v, hy];
    have he1: affine (1:Signed) y₀ 0=y₀:=by simp [affine]
    have he2: affine (1:Signed) b 0=b:=by simp [affine]
    simp only [he2,show affine (1:Signed) ((μ).ratio.embed b) 0=(μ).ratio.embed b from he1,norm_one,scalar_z,one_mul,one_smul] at hp'
    exact hp'
end YM.MergeProof.Ribbons.ManyCopies.Stem
