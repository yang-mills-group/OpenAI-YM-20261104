import YM.LocalLTE.Tol.Fame
import YM.LocalLTE.Georges.Field
/-!
# Real calibrated cylinder supplies. Hold section stencils including cover placement. All LABEL directions in calibrated canonical finite requests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port.Sect
open Filter Function Set Lattice Wilson Labels Overlay Marker Source RG Finset Pressure MeasureTheory Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Animals FrameBox Grove Cabana
open Work.H03 Next.Foundations ConnectedActivityE6 Blaze Brush
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{d k:ℕ}
set_option quotPrecheck false
-- before schedule choose b
variable {V α:Type}[DecidableEq V] [Fintype V][Fintype α]
variable (R: Marker.Census V)
open Extra.Histories RG.Supply Supply
open LoopBank
variable {n:Side}
structure School (G:Gauge)(R:Marker.Census V)(α:Type)(n:Side) where
   origin : V→ Site n
   units : V→ ℂ
   demand : α→ℕ
   coeff : ∀ i, (Labels.frames G|>.level (demand i)).Coeff
   center : α→Site n
   mode : α → R.Mode
namespace School
variable (S: School G R α n)
structure Permits (d b:ℕ)(z:ℝ):Prop where
   lits i : S.demand i ≤ d
   links i j: j∈(S.mode i).val→ S.origin j ∈ neighbors (b+1) (S.center i)
   wages i : (Labels.frames G|>.level (S.demand i)).coeffSize (S.coeff i) ≤ z
   anchors i: (S.mode i).val.Nonempty
variable (g:(i:α)→ Grove (S.center i))
local notation "T" j=> (Labels.frames G|>.level j)
def signal (i:α):= (localSection G (S.demand i)).places (S.coeff i) (S.center i)
variable (P:Rep G n)(b k':ℕ)(κ:ℝ)
open Extra.Trajectories
open Progress.DirectedRecipe PhysicalNext.Repeat.Mallow
local notation "S'"=> (fun i=>neighbors (b+1) (S.center i))
abbrev layoutL : Layers P R α:=⟨S.origin,S.units,S',S.mode, School.signal R S⟩
def exposed(i:α):= argL G (S.demand i) k' (S.center i) (g i) b κ (S.coeff i)
variable [Nonempty V]
abbrev billed : Cadence R P:= ⟨posta P R (layoutL R S P b),Port.crystal P (layoutL R S P b) (exposed R S g b k' κ),Port.thaw P (layoutL R S P b) (exposed R S g b k' κ)⟩
-- adapt generic budget portion using dummy LoopBank remainder accounting! Preserves layout only. estimates.Proof.Author
variable {J M CB A':ℕ} {μ ζ x:ℝ} {L:Side}{F:Stage}(h:Etes G J b M CB μ ζ κ k' L F x) (hr:Permits R S J b ((betaF G x L)^μ))
local notation "Y"=> betaF G x L
local notation "f"=> slotPay G (payT G J F.power F.order) b F.order F.power
local notation "z0"=> (Y^μ)
local notation "v"=> Y^(-ζ)
local notation "s"=> (neat Y μ)
local notation "ν"=> PhysicalNext.Repeat.Urns.divisor Y
local notation "K"=> (layoutL R S P b)
local notation "TΩ"=> (billed R S g P b k' κ)
local notation "C" X=> costAP M s P.p b X z0
local notation "w0"=> (fun _:V=> s)
local notation "mℓ"=> ((L).val*radiusB x)
omit [Fintype V] [Fintype α] [Nonempty V] in
lemma dummyL {t' : ℝ} (hr:Permits R S J b t'): ∃ T1: LoopBank G n R α,T1.origin=S.origin∧ T1.units=S.units∧ T1.select=S.mode∧ T1.scene=S.center ∧ T1.Legit R b 1 0:=by
    let T':=LoopBank.mk (n:=n) (G:=G) (R:=R) S.origin S.units S.mode (fun _=>[]) S.center (fun _=>0) (fun _=>true) (fun _=>0)
    refine ⟨T',rfl,rfl,rfl,rfl,⟨hr.anchors,fun _=>Nat.zero_le _,fun _=>norm_zero.le,fun i u=> ?_,fun _=>rfl,fun _ _ _=>rfl,hr.links,⟨zero_le_one,le_rfl⟩⟩⟩
    simp [T']
variable (hp0:P.p.threshold=temp (betaF G x L))(hp:P.p.power=F.power)(ho:P.p.order=F.order)(he:P.p.supportExponent=F.supportExponent) (hc: HasSlots P.p P.activities)
    {a f0 t:ℝ}(hV: P.activities.Valid P.p t ((PhysicalNext.Repeat.Urns.divisor (betaF G x L))^2))
    (hm:2*(b+1) < n.val)(hj:2*(2*b) ≤ n.val)
    (hT: Fintype.card V ≤ CB)(hN:Fintype.card α ≤ M)
    (hf:∀ i,neat (betaF G x L) μ*‖S.units i‖≤ a)
    (hw:0 ≤ μ)
local notation "aℓ" X=> payment P.p z0 X b
include h hr hp0 hp ho he hc hV hm hj hT hN hf hw
lemma shipping (i:ℕ)(hi:k'≤ i+1): Cadence.Factor R TΩ a (C f) (C (f+v)) v v (C v) ν w0 ∧ Port.Shine R (TΩ).plan i mℓ κ ∧ Port.capacity P.p V (C (f+v)) (C v) ν v (Y^ζ) mℓ ≤ Y^(-(1:ℝ)) ∧ ∀ U,(TΩ).sure.density U=(P.eval U:ℂ) • Marker.Poly.pass (Layers.logPart K U):=by
    obtain ⟨hB,_,hS,hY⟩:= h.cash
    have hρ:= hY V hT P.p ho hp he hp0; let μ':=v; let D:= s; let k:= K; let Mℓ:= (mℓ)
    have hz : 0<Y:=zero_lt_one.trans_le hB; have hv:0≤ (Y^μ):=Real.rpow_nonneg hz.le _; have hs:0<D:=Real.rpow_pos_of_pos hz _; have hd':D≤1:=Real.rpow_le_one_of_one_le_of_nonpos hB (by linarith only [hw])
    have hF:0≤f:=by
       have hh:=payBig G J b J le_rfl F.power F.order; exact ((zero_le_one.trans (Next.Foundations.price_one_le ..)).trans (le_max_right ..)).trans hh.2 -- orientation
    have hl:0≤ Y^(-ζ):=Real.rpow_nonneg hz.le _; have hv':0 < ν:=PhysicalNext.Repeat.Urns.nonzero _
    obtain ⟨Y',hX,ht,hp',hh,hT'⟩:= S.dummyL R b hr -- order
    have hyg: (K).region= Y'.wires R b:=by unfold wires; funext i; dsimp only; rw [hh] 
    have hy: (K).tag=Y'.select:=hp'.symm
    let u x:= payment P.p z0 x b
    have hu (x:ℝ)(hg:0≤x):0≤ u x:=mul_nonneg (mul_nonneg hv (sunny ..)) hg
    have hj':= LoopBank.priceFire P R Y' b hT' w0 (fun _=>hs) (η:=D) (fun _=>le_rfl) hd' hs.le
    let Xx j:=(signal R S j); let Yy:= exposed R S g b k' κ
    have hh' (j:α) := h.lights _ (hr.lits j) n P.p hp0 ho hp hm hj (S.center j) (S.coeff j) (g j) (hr.wages j)
    have he' (j) : P.p.Regular (S' j) (Xx j) ∧ P.p.supBounds (S.center j) (S' j) (Xx j) (Y^μ*f)∧ P.p.Regular (S' j) (Yy j) ∧ P.p.supBounds (S.center j) (S' j) (Yy j) (Y^μ*(f+μ')) ∧ P.p.Regular (S' j) (Xx j-Yy j)∧ P.p.supBounds (S.center j) (S' j) (Xx j-Yy j) (Y^μ*μ') ∧ ∀ U,‖Xx j U‖ ≤ Y^μ*f:=hh' j
    have hrℓ(j)(i)(hi:i∈(S.mode j).val) (f':Config G n→ℂ)(x':ℝ)(hf:P.p.supBounds (S.center j) (S' j) f' (Y^μ*x')): P.p.supBounds (S.origin i) (S' j) f' (u x') :=by
         let y:ℝ:=1+(↑(b+1):ℝ); let u':= f'; have hχ:1+(separation (S.center j) (S.origin i):ℝ) ≤ y:= add_le_add_right (Nat.cast_le.mpr ((neighbors_mem ..).1 (hr.links _ _ hi))) _
         have hh:1 ≤ y:=le_add_of_nonneg_right (Nat.cast_nonneg _); have h: u x'=y^(P.p.power*P.p.order)*(Y^μ*x'):=by unfold u payment y sonic; ring
         rw [h]; refine ⟨mul_nonneg (pow_nonneg (zero_le_one.trans hh) _) hf.1,fun U h' z hz hv=>?_⟩
         rw [pow_mul]; exact (Extra.Multi.Germs.relocated_bound hχ hf h' _ hz hv).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_pow₀ hh) hz) hf.1) -- CA.V.
    have hg:(K).Ready:= ⟨⟨hr.anchors,hr.links⟩,fun j=> (he' j).1 ⟩ -- notation parser
    have hyT:= Port.frostD P R K hc hg hV
    let f1:= f; let a':= z0*f; have ha':0≤a':=mul_nonneg hv hF; let p₀:= ν
    have hpV(j:α)(U): ‖Layers.residual K j U‖≤ a':=by unfold Layers.residual; split; simp [ha']; exact ((he' j).2.2.2.2.2.2 U)
    have hQ: chargeFog P K ((ν)^2)*chargeMark P K (fun _=>a') w0 ≤ μ'*ν:=by
       -- generic principle.Spire
       let p:= P.p; let z':= chargeFog P K ((ν)^2); have hi' : (coastK P (K)).card ≤ M*ballCost (b+1):=by unfold coastK; rw [hyg]; refine (card_biUnion_le ..).trans ((sum_le_sum (g:=fun _=>ballCost (b+1)) fun i _=> neighbors_card _ (Y'.scene i)).trans ?_); simpa using Nat.mul_le_mul_right (ballCost (b+1)) hN
       let F0:= footprintCost b P.p.supportExponent*a'; have h0:0≤F0:=mul_nonneg (Real.exp_nonneg _) ha'
       let Q:= ν^2; have h0':0≤Q:=sq_nonneg _; have hu:z'≤ fog M b Q:=sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hi') h0')) _
       let x':=chargeMark P K (fun _=>a') w0
       have he''(i:α):0 ≤ Poly.toll w0 ((K).tag i)*P.p.mass (K|>.region i) a':=mul_nonneg (Poly.worth (fun _=>hs) _).le (mul_nonneg (Real.exp_nonneg _) ha')
       refine le_trans (mul_le_mul hu (show x'≤ (1+F0)^M from ?_) (Finset.prod_nonneg («s»:=Finset.univ) (fun i _=> add_nonneg zero_le_one (he'' i))) (show 0≤ fog M b Q from sub_nonneg.mpr (Real.one_le_exp (by positivity)))) hρ.2.1
       unfold x' chargeMark; rw [hyg,hy]; apply le_trans (Finset.prod_le_prod (g:=fun _:α=>1+F0) ?_ ?_) _ -- edits
       · rw [←hyg,←hy]; exact fun i _=> add_nonneg zero_le_one (he'' i)
       · intro i hi; refine add_le_add_right (?_) _; exact (LoopBank.spaceZ P R Y' b hT' w0 (fun _=>hs) (η:=D) (fun _=>le_rfl) hd' a' ha' i).trans (mul_le_of_le_one_left h0 hd')
       rw [prod_const,card_univ]; exact pow_le_pow_right₀ (le_add_of_nonneg_right h0) hN
    have hvol(x:ℝ)(hx:0≤x)(y:V):SumBudget (fun j=> if y∈((K).tag j).val then Poly.toll w0 ((K).tag j)* P.p.mass (K|>.region j) (u x) else 0) (C x):=by rw [hyg,hy]; exact hj' (u x) (hu _ hx) M hN y
    have hV':= Port.frosty P K hc hV (fun _=>a') (fun _=>u f) hpV (fun _=>hu f hF) (fun i t h=>hrℓ i t h _ _ (he' i).2.1) (w0) (fun _=> hs) μ' a (C f) (ν) hf hv' hQ (hvol f hF)
    have ht:=Port.starsV P K Yy (fun i=> (he' i).2.2.1) (fun i=> (he' i).2.2.2.2.1) hyT
    obtain ⟨hd,hg'⟩:=Port.pollen P K Yy hV' hl (fun _=>u (f+μ')) (fun _=>u μ') (fun i=>hu _ (add_nonneg hF hl)) (fun i=>hu _ hl) (fun i t hi=>hrℓ i t hi _ _ (he' i).2.2.2.1) (fun i t hi=>hrℓ i t hi _ _ (he' i).2.2.2.2.2.1) (hvol (f+μ') (add_nonneg hF hl)) (hvol _ hl)
    refine ⟨⟨hyT,hV',ht.1,hd,ht.2,hg',Port.cleansed P K Yy⟩,?_, hρ.1, Port.nocturne P R K hc hg hV ⟩
    refine Port.appeal P K Yy fun j=> ⟨S.center j,(neighbors_mem ..).2 (by rw [separation_self]; exact Nat.zero_le _),fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hS), b,by change b+1≤ Mℓ at hS; omega, g j,fun x=>Sect.goods G _ _ _ _ b κ (S.coeff j) x i hi⟩
end School
end YM.LocalLTE.Port.Sect
