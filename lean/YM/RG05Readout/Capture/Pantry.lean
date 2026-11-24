import YM.RG05Readout.Many.Iota
/-!
# Inbox while clustering

Besides the Served board, store stronger exponents and coherence for every
counter path on the last step. This permits performing group prediction on
all copies and in ALL anchored trials (subject to Census); not just choosing
a density rep from marginals. `alcove`: evaluate all tested simultaneous
supports exactly. It does not itself install new stencils at the output labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge} {m p N d:ℕ}{V W : Type}[DecidableEq V] [Fintype V][DecidableEq W][Fintype W] {R:Census V}{B:Census W}{a b c e t y z α β f:ℝ}
section
variable {n:Side}
structure Alcove (Q:Rep G n)(P:V→Three G n)(F: Config G n→ Poly R) (o:V→Site n)(w:V→ℝ)(t a c:ℝ):Prop where
    clef : ∀ i,Dominated ((P i).snd.2)
    value U : (F U).part R.quiet=Q.eval U
    tally i U : (F U).part (R.fire i)=(P i).1 U
    price i : coin Q ((P i).2.1) ((P i).2.2)=(P i).1
    chamber : ∃ (H:Support n→ Config G n→ Poly R) (K:Box n→ Config G n → Poly R) (ψ:V→Response G n)(ν:V→ℂ), Towed w id H Q.p.B (Q.p.supportExponent+1/2) 1 ∧ Towed w Prod.fst K Q.p.B (Q.p.supportExponent+1/2) t ∧
        (∀ j,Burns o j (H j) Q.p.threshold)∧ (∀ j,Flow o j (K j) Q.p.threshold)∧ Garnish Q.p o ψ w (Q.p.supportExponent+1) a ∧ (∀ i,w i*‖ν i‖ ≤ c)∧
        (∀ i U,(K i U).part R.quiet=profile Q.activities (fun j=>Complex.ofReal ∘ Q.activities.K j) i U)∧ (∀ j i U,(K i U).part (R.fire j)+hook Q.activities Q.p.threshold (ψ j) i U=profile Q.activities ((P j).2.2) i U)∧ F= play Q R K (fun U=> Mach R ν+∑ i,H i U)
-- NOTE at this port F might not integrable; caller supplies AFTER omission. doesn't assert analytical binding without purchase. o roots always original.
end
section
variable {A : RG.History G}
local notation "R₀"=> A.rep N p m
local notation "R₁"=> A.rep N p (m+1)
local notation "O"=> A.levels.clock.op m p
variable {D:GaugeDoor (A.rep N p (m+1)) (A.rep N p m)} {r:ℕ→ℕ} (he:Coursework A r D a b c)
variable {P:V→ Three G (A.S.side (m+1) p)} {Q:V→Three G (A.S.side m p)} {F: Config G (A.S.side (m+1) p)→Poly R} {o: V→Site (A.S.side (m+1) p)} {w l:V→ℝ}{ν:V→ℂ}
local notation "Ξ"=> A.levels.budget m
local notation "Δ"=> A.levels.budget (m+1)
local notation "Λ"=> ((O).ratio.parent ∘ o)
local notation "κ!"=> fun i:V=> (ν i)⁻¹ • Q i
include he
set_option maxHeartbeats 800000 in
lemma Coursework.plates (h:A.Selected) (hm:m<N)(hk:MenuBoard (R₁) P F o w t 1)(hy:(Δ).supportExponent-4≤t)
    (hr:∀ i,1 ≤ ‖ν i‖)(hp:∀ i,0<w i)(hL:∀ i,Ride (O) (o i) ((Λ) i) D (ν i) (P i) (Q i) (l i))
    (ho:Occupancy o (r m))(ho':Occupancy (Λ) (r m))(hf:∀ i,2*w i*l i≤1):
    Alcove (R₀) κ! ((O).push (R₁).beta F) Λ (fun i=> a*w i) c a (1/2):=by
    -- charges id at last aperture. get Inventory before restoration peg.
    have h1:= h.represents N p (m+1) hm; have h0:= h.represents N p m hm.le; let S:=(O).push (R₁).beta F; let W i:=a*w i
    have hu:= he.poses; have ha:=hu.hats; have hW(i):0<W i:=mul_pos ha.1 (hp _)
    have ht := he.publishes; let s₁:=(R₁).p; let s₀:=(R₀).p; have hx: (Ξ)=s₀:= h0.vac.symm; have hv:(Δ)=s₁:= h1.vac.symm
    have hR(i): Ride (O) (o i) ((Λ) i) D 1 (P i) ((κ!) i) (l i):=by
       have he:= (hL i).matchPay 1 (ν i)⁻¹ 1 (show _=_ from by rw [inv_mul_cancel₀,one_mul]; exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hr i))); rw [one_smul,norm_one,norm_inv,max_eq_left (inv_le_one_of_one_le₀ (hr _)),one_mul] at he; exact he
    choose χ hχ μ hμ hM using fun i=> (hR i).pays; let Z:=κ!; let Y i := (Z i).snd.1; let K i:= (Z i).snd.2; have hY (i):Useful (R₀) (Z i):= (hR i).tomorrow
    have hO'S:= A.levels.transition_mass m p ((R₁).beta)
    have hU(i:V)(U): (S U).part (R.fire i)=(Z i).fst U:=by
       have hQ : (fun V=>(F V).part (R.fire i))=(P i).fst:= funext fun V=>(hk.check h1.good.labels V).2 i
       have hO := push_get (φ:=F) hO'S hk.cleared (R.fire i); rw [hQ,← one_smul ℂ ((O).push _ (P i).fst),← (hR i).exactStep] at hO; exact congr_fun hO U
    let u':=(Δ).supportExponent-4
    have h' := hk.grants.prune (d:=a) hp hW (slighter hp hW (w:=a) (by intro i;rfl) ha.1.le ha.2) ha.1.le (show u'+0≤ t from by rwa [add_zero]) (le_of_eq (mul_one a))
    have he1 : 0≤ u':=by unfold u'; linarith only [hu.exp.2]
    have he2 : u'+1≤ (R₁).p.supportExponent:=by unfold u'; rw [hv]; unfold s₁; linarith only
    have hk0(i): 2* W i*l i ≤ a:=by unfold W; rw [show 2* _ * _ = a*(2*w i*l i) from by ring]; exact mul_le_of_le_one_right ha.1.le (hf _)
    have hZ (i): W i*l i≤a:=by linarith only [ha,hk0 i,ha.1] -- ha not relation
    obtain ⟨I,i,Q₀,H,ψ,hψ,hΞ,hW₀⟩:= inventory hW ht.contact ht.tunes ht.propagate h1.good h' he1 he2 (H:=D) (S:=O) (ν:=μ) (k:=fun i=>profile (R₀).activities (K i)) (fun i=>⟨χ i,hχ i,hM i⟩) ho ha.1.le hk0 hZ (p:=(Ξ).supportExponent+1) (by rw [hx]; unfold s₀; linarith only)
    have hF := hu.copper; dsimp only at hF; rw [hv] at hF; obtain ⟨F₀,K₀,hf₀,hf₁,hK₀,hK₁,hP₀,hX₀,hL₀⟩:= (ht.reserves Q₀ hW ho' (H.fatten hF)).buyer
    let Y' U:= Mach R μ +∑ i,F₀ i U
    have hS : S=play (R₀) R K₀ Y':=by
       funext U; unfold S; rw [show F= _ from funext hW₀,convective (O) _ _ hO'S (heat Q₀ (O) W h1.good),hP₀]
       unfold Y' play
       rw [pass_add (mute R μ) (by rw [Poly.part_sum]; exact Finset.sum_eq_zero (fun j _=> (hf₁ j).sil U)),mul_smul_comm,mul_assoc]
    refine ⟨fun i=> (hY i).normK,fun U=>?_,hU,fun i=> (hY i).read, F₀,K₀,ψ,μ,?_,?_,hf₁,hK₁,?_,?_,hX₀,fun j i U=>?_,hS⟩
    · change (S U).part _ = _; rw [hS]; apply bronze; exact h0.good.labels; exact fun i=>hX₀ i U; unfold Y'; rw [Poly.part_plus,mute,zero_add,Poly.part_sum]; exact Finset.sum_eq_zero fun i _=> (hf₁ i).sil U
    · rw [hx] at hf₀; exact hf₀
    · apply hK₀.shrink ?_ le_rfl hW; rw [hx]; unfold s₀; linarith only
    · rwa [hx] at hψ
    · intro i; change W i*‖μ i‖ ≤ 1/2; exact (mul_le_mul_of_nonneg_left (hμ i) (hW _).le).trans (by linarith only [hk0 i,ha.2])
    · rw [hL₀]; exact (congr_fun (hΞ j i) U).symm
end
end YM.RG05Readout.Many
