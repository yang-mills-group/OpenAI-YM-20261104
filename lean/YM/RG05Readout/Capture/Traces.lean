import YM.RG05Readout.Capture.Room
/-!
# Accounting out of actual packet from measuring interval

Redemption uses last step with all preimages. No requirement on total marker
load. Physical policies remain contravariant and choose all legitimate cluster
products in output slots. Charges one coupon BEFORE repaying adjustment on
ancestors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G}{m p N n:ℕ}{V W : Type}[DecidableEq V] [Fintype V][DecidableEq W][Fintype W] {R:Census V}{B:Census W}{a b c d t y z β:ℝ}
set_option quotPrecheck false
local notation "X"=> C.path
local notation "R₀"=> C.path.rep N p m
local notation "R₁"=> C.path.rep N p (m+1)
local notation "Ξ"=> C.path.levels.budget m
local notation "ξ"=> C.side (m+1) p
local notation "π"=> C.side m p
local notation "K"=> C.path.levels.clock.op m p
local notation "ψ"=> (K).ratio
local notation "L"=> C.S.block m
local notation "O"=> Address.Bud C p m
variable {o:W→Site (C.side m p)}{ν:V≃W×Address.Bud C p m}{x:V→Site (C.side (m+1) p)}{δ:W→Motion}
local notation "λ₀"=> Prod.fst ∘ ν
local notation "z!"=> fun i:ℕ => ((L).val:ℂ)^i
variable {P: V→Three G (C.side (m+1) p)} {A:Config G (C.side (m+1) p)→Poly R} {s:W→ℕ}{Θ:W→Body}{w: V→ℝ} {r:ℕ→ℕ}{j:W→ℝ}{B₁:W→ℝ}
variable (h:C.Makes)
variable {T: W→Tape G (C.side (m+1) p)} {S:W→Tape G (C.side m p)}
local notation "φ"=> fun i:V=> (((L).val):ℂ)^s (λ₀ i)
local notation "shuttle" => fun i:O=> Native.pull (Address.displacement C p m i) (((C.S.block m).val:ℝ)⁻¹)
section
variable {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} {σ t' u v:ℝ}
-- reusable per-parent report
include h
lemma report_one (hO:SoundDoor (K) D)(t:Motion)(o:Site π)(V S f)(i:ℕ)(Q:ℝ)(hm:m<N)(μ:(R₀).activities.Moves t.1 o)(he:Train (D:=D) (keys0 h hm) (d:=i) V S Q)(hx:Cap (i+2) f 1):
    ∃ P':O→Three G π, View.spin t μ (S f)=average P' ∧ ∀ (a:O)(P:Three G ξ), Useful (R₁) P → Signpost R₁ t (affine t.1 ((ψ).embed o) (child C p m a)) (V ((shuttle a) f)) P→ Ride (K) (affine t.1 ((ψ).embed o) (child C p m a)) o D (z! i) P (P' a) Q:=by
    obtain ⟨f',hq,rfl⟩:= he
    refine ⟨fun a=> View.spin t μ ((f' a) f), ?_,fun a P he' hp=> ?_⟩
    · unfold Address.average; let r':=(Fintype.card O:ℂ)⁻¹; rw [LinearMap.smul_apply,LinearMap.sum_apply,View.spin_real,View.spin_sum]; unfold Motion.scalar; split; simp; rfl
    have hκ: Motion.scalar t (z! i)= z! i:=by unfold Motion.scalar; split; simp; rfl
    have hT := hq a f 1 hx; rw [mul_one] at hT
    have hR: Ride (K) (affine t.1 ((ψ).embed o) (child C p m a)) (affine t.1 o 0) D (z! i) P _ Q := View.paid h hm hO hκ hT he' (View.signpost_use h hm.le _ μ hT.tomorrow) (hp.at_child View.shift_at) (View.spin_at t μ)
    rwa [show affine t.1 o 0=o by simp [affine]] at hR
variable (hc:Coursework C.path r D a b c) (μ:∀ i,(C.path.rep N p m).activities.Moves (δ i).1 (o i))
variable {z:V→ℝ}{Z:W→ℝ}
local notation "σ'"=> fun i:V=>budwgt C p m (s (λ₀ i))
include h hc
lemma budholds (hm:m<N) (H:∀ i:W,Train (D:=D) (keys0 h hm) (d:=s i) (T i) (S i) (j i))
    (hx: MenuBoard (R₁) P A x w d 1)(hp:(C.path.levels.budget (m+1)).supportExponent-4≤d)(ho:Occupancy ((ψ).parent ∘ x) (r m)) (ho':Occupancy x (r m))
    (hf:∀ i:V,x i=affine (δ (λ₀ i)).1 ((ψ).embed (o (λ₀ i))) (Address.child C p m (ν i).2)) (hg:License B R λ₀)
    (hb:∀ i:V,let v:=(λ₀ i); Signpost (R₁) (δ v) (x i) ((T v) ((shuttle (ν i).2) (Θ v))) (P i))
    (ht:∀ i, Cap (s i+2) (Θ i) 1) (hw:∀ i,0 < w i)
    (hℓ:∀ i:V,2*w i*j (λ₀ i) ≤ 1) (hZ:∀ i,0< Z i) (hF:∀ i:V, Z (λ₀ i)* ‖σ' i‖ ≤ a*w i/(Fintype.card (Address.Bud C p m):ℝ)):
    Alcove R₀ (fun i=> View.spin (δ i) (μ i) ((S i) (Θ i))) (fun U=> feed σ' hg ((K).push (R₁).beta A U)) o Z c a (1/2):=by
    choose p' hp' hP using fun i=> report_one h hc.publishes.propagate (δ i) (o i) _ _ (Θ i) _ _ hm (μ i) (H i) (ht i)
    let e:= λ₀; let K' i:= p' (e i) (ν i).2
    have hV := parentExact hf; have hU(i): Ride (K) (x i) ((ψ).parent (x i)) D (φ i) (P i) (K' i) (j (e i)):=by
       let q:=e i; let b':=(ν i).2; have hx':= hb i
       dsimp only at hx'; rw [hf] at hx'; rw [show (ψ).parent (x i)=o q from congr_fun hV i, hf i]; exact hP q b' (P i) (hx.fettled _) hx'
    have hL(i:V):1 ≤ ‖φ i‖:=by rw [show φ i=(↑((L).val):ℂ)^(s (e i)) from rfl,norm_pow,Complex.norm_natCast]; exact one_le_pow₀ (by exact_mod_cast (C.S.block m).property)
    have he':= hc.plates h.wilson hm hx hp hL hw hU ho' ho hℓ
    have hw'(i):0<a*w i:=mul_pos hc.poses.hats.1 (hw i)
    have hB:∀ k:W,(Finset.univ.filter fun i:V=> (λ₀ i)= k).card ≤ Fintype.card O:=by
       intro i; let U:=Finset.univ.filter fun j:V=>e j=i; let f:=fun j:V=>(ν j).2; calc U.card=(U.image f).card:= (card_image_of_injOn (fun i hi j hj he=> ν.injective (Prod.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) he))).symm
                                                                            _ ≤ _:=Finset.card_le_univ _
    rw [show (fun i=>spin (δ i) (μ i) ((S i) (Θ i)))=fun i=> average (p' i) from funext hp', ← ave_merge (ν:=ν) (s:=s) p']
    exact he'.group σ' (h.wilson.represents N p m hm.le).good (StepData.push_integrable (C.path.levels.transition_mass ..) _ hx.cleared) hV Fintype.card_pos hc.poses.hats.1.le (by norm_num) hw' hZ hF hB
end
-- root stencil height exactly n.Place roots nontrivial equiv.
variable (x:W→Site (C.side n p))(v:W→Motion)
local notation "E"=> ManyStem C x
local notation "U"=> Mine.tree x v
lemma Mine.equal_site (x:Site (C.side n p))(h:n≤ n): (C.S.toDepth h p).parent x=x:=by
    let u:=(C.S.toDepth h p); have he : u.count.val=1:= Nat.eq_of_mul_eq_mul_left (C.S.side n p).property (u.exact_size.symm.trans (Nat.mul_one _).symm)
    have ht : u.embed x=x:=by rw [Ratio.embed,he,one_smul,Lattice.wrap_lift]
    exact ((congr_arg u.parent ht.symm).trans (Ratio.embed_parent ..))
omit [DecidableEq W] [Fintype W] in
lemma Mine.carried (i:ManyStem C x n): (U).supportX n i=x i.val.1:= (Mine.equal_site i.val.2 (le_refl n)).symm.trans (i.property (le_refl n))
def Mine.remap : ManyStem C x n ≃ W where
    toFun i:= (U).labelY n i
    invFun i:= ⟨(i,x i),fun h=> Mine.equal_site (x i) h⟩
    left_inv i:=Subtype.ext (Prod.ext rfl (show x i.val.1= _ from (Mine.carried x v i).symm))
    right_inv _:=rfl
lemma solo_com_link (v:E n→Three G (C.side n p))(f:E n≃W):combine (fun i=>f i) (fun _=>1) v= v ∘ f.symm:=by
   funext j; unfold combine; rw [sum_eq_single (f.symm j)]; simp; intro p _ hp; rw [if_neg (fun h=>hp (f.injective (h.trans (f.apply_symm_apply _).symm))),zero_smul]; simp

lemma Alcove.squeeze (h:C.Makes){A:Census W}{I:E n→ Three G (C.side n p)} {F:Config G (C.side n p)→Poly (Mine.ward x v A n)}{w:ℝ}{t e u:ℝ}
    (hW:n≤N)(hz:Alcove (C.path.rep N p n) I F ((Mine.tree x v).supportX n) (fun _=>w) t e u) (he:Integrable F (prior G _))(hx:0<w)(hp:0≤e)(hu:0≤u):
    Alcove (C.path.rep N p n) (I ∘ (Mine.remap x v).symm) (fun U'=>feed (fun _=>1) (YM.RG05Readout.Many.chamber (V:=E n) A ((U).labelY n)) (F U')) x (fun _=>w) t e u:=by
    let L':=Mine.remap x v
    rw [← solo_com_link x I L']; apply hz.group (fun _=>1) (h.wilson.represents N p n hW).good he (funext fun i=> Mine.carried x v i) (N:=1) (by norm_num) hp hu (fun _=>hx) (fun _=>hx) (fun i=>by rw [norm_one,mul_one]; simp) _
    intro j; apply card_le_one.mpr; intro i hi k hk; exact L'.injective ((mem_filter.mp hi).2.trans (mem_filter.mp hk).2.symm)
end YM.RG05Readout.Many
