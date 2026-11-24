import YM.SignedWilsonExpansion.Purchase.Sable
import YM.SignedWilsonExpansion.Purchase.Preflight
/-! Polynomials with costs holding the underlying cutoffs completely fixed at N,p.

This page only charges the **carry** (not Chronicle.read of all masks).
Use Bornm and only then multiply K restoration costs.
-/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases
open PhysicalNext.Repeat.Quince.PreCost WilsonCoeffUV.Bank Function Filter Matrix Lattice RG Wilson Gauge Extra.Histories Analysis
open WilsonCoeffUV.Mer.Xa.FetchP Extra.Histories.Motion Labels Trace.Physical.Germ Trace.Physical.GermGraph
open Source
open scoped Classical ContDiff BigOperators Topology
variable {G:Gauge} {d i j l b n c N p r h:ℕ}{C:Family G}{F:Frame G d}{Y ν:ℝ}
-- exact '
local notation "F₀" => (C.labels.level d)
local notation "H₀" => C.path
local notation "Θ"=> C.path.levels.clock.threshold
namespace PurchVoice
open Work.G08
variable (P:PurchVoice C d N p j n)
variable {T:ℕ→ (C.label d →ₗ[ℂ] C.label d)}
abbrev Needed (C:Family G)(d j n N p:ℕ)(Y ν:ℝ)(P:ℕ→(C.label d→ₗ[ℂ] C.label d)): Prop:=
    ∀ i∈ Finset.Ico j (j+n), CapsuleAt C.path.levels.clock.threshold (C.labels.level d) C.path C.params (C.localSection d) i N p (Y^(d+1)) ν (P i)
def TowerS (d:ℕ):Credit := Credit.leanC.powC (d+1)
def recoverDose (F:Frame G d):Credit:= (bound_ledger' F (TowerS d)).choose
abbrev chargeS (F:Frame G d): Credit:= (bound_ledger' F (TowerS d)).choose_spec.choose
abbrev resUrgent (F:Frame G d): Credit:= (bound_ledger F (TowerS d)).choose
structure FrontStep (C:Family G)(d j n N p:ℕ)(Y ν:ℝ)(P:ℕ→ (C.label d→ₗ[ℂ] C.label d)): Prop where
     Need: Needed C d j n N p Y ν P
     y : 1≤Y
     cost : 0≤ν
     small : (recoverDose (C.labels.level d)).buy Y*ν≤1/2
     bill : (n:ℝ)≤Y
variable (g: C.Makes)(u:FrontStep C d j n N p Y ν T){A:C.label d≃ₗ[ℂ] C.label d}(hp:ReadyReturn C d N p j n A)
include u
lemma search_cost {i:ℕ}(h:i∈ Finset.Ico j (j+n))(v:C.label d): (F₀).coeffSize ( P.charges i v-T i (P.charges (i+1) v)) ≤ ν*((F₀).coeffSize (P.charges i v)+(F₀).coeffSize (P.charges (i+1) v)):=let ⟨h',t⟩:= Finset.mem_Ico.mp h; (u.Need i h).price _ _ _ (P.bought _ (Finset.mem_Icc.mpr ⟨h',t.le⟩)) (P.bought _ (Finset.mem_Icc.mpr ⟨by omega,t⟩)) (P.blast_step i h v)
lemma ledger: ledgerC F₀ T ((TowerS d).buy Y) (i:=j) (l:=j+n):=fun i h=> by rw [TowerS,Credit.power,Credit.lean_cost]; exact (u.Need _ h).carries
lemma rights (w:C.label d): peak F₀ j (j+n) (fun i=> P.charges i (P.finalX w)) ((chargeS F₀).buy Y*(F₀).coeffSize (P.pollAt w)) :=
    (bound_ledger' F₀ (TowerS d)).choose_spec.choose_spec Y u.y ν u.cost u.small j _ (by omega) (by rw [Nat.add_sub_cancel_left]; exact u.bill) _ T (ledger u) (fun _ h=> search_cost P u h _)
include g u P hp
abbrev pollS (F:Frame G d)(Y:ℝ): ℝ:=2*(chargeS F).buy Y -- no include? included? defs
lemma capPrice (w:C.label d): peak F₀ j (j+n) (fun i=> P.charges i (P.finalX w)) (pollS F₀ Y*(F₀).coeffSize (A w)):= by
    intro i t; unfold pollS; have hv:0≤ (chargeS F₀).buy Y:= zero_le_one.trans (Credit.purchase _ u.y); exact (( rights P u w ) i t).trans ((mul_le_mul_of_nonneg_left (gruesome P g hp w) hv).trans_eq (by ring))
lemma worth (v:C.label d): (F₀).coeffSize (A.symm v)≤ pollS F₀ Y*(F₀).coeffSize v:= by
    have U:= capPrice P g u hp (A.symm v) (j+n) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩); change (F₀).coeffSize ((P.path (j+n)).index ((P.path (j+n)).index.symm (A.symm v))) ≤ _ at U; rwa [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at U
-- absolute difference from homogeneous top-weight & rank, actual calibration e not fit shrink. Scale Θ reinsert.
abbrev money (F:Frame G d)(Y ν η:ℝ): ℝ:= 2*η+ν*(pollS F Y+pollS F Y)
abbrev chipAt (C:Family G)(j k r:ℕ):ℂ:= ((↑ (C.path.levels.clock.threshold k/ C.path.levels.clock.threshold j) ):ℂ)^r
lemma halfPlease (w v:C.label d) (r:ℕ)(h: ∀ i, v i≠0→ (F₀).grades i=(d,r)) : (F₀).coeffSize (w-chipAt C j (j+n) r • v)≤(resUrgent F₀).buy Y*((F₀).coeffSize (A w-v)+money F₀ Y ν (tollQ C d j p)*(F₀).coeffSize (A w)):=by
    let L:=(F₀).coeffSize (A w); have Hl:0≤L:=size_nonneg ..; let D:=pollS F₀ Y; have H:1≤D:= ( (chargeS F₀).purchase u.y ).trans (le_mul_of_one_le_left (zero_le_one.trans ((chargeS F₀).purchase u.y)) one_le_two) -- notation H ok
    let B:=ν*(D+D)*L; have hD:0≤ D:=zero_le_one.trans H; have hB:0≤ B:=mul_nonneg (mul_nonneg u.cost (add_nonneg hD hD)) Hl
    let W(i):= P.charges i (P.finalX w); let T'(i):= chipAt C j i r; let R(i):= T' i• v; let V(i):= W i-R i
    have Hv (i):0< Θ i:= (C.path.levels.budget i).threshold_pos
    have ht (i:ℕ)(hp: i∈ Finset.Ico j (j+n)): T i (R (i+1))= R i:=by
        unfold R; rw [map_smul,(u.Need _ hp).tunes r v h, smul_smul]; apply congr_arg (fun t:ℂ=>t•v); unfold T' chipAt; rw [←mul_pow]; congr 1; rw [←Complex.ofReal_mul]; exact congr_arg ((↑):ℝ→ℂ) (by field_simp [ne_of_gt (Hv i), ne_of_gt (Hv (i+1)),ne_of_gt (Hv j)])
    have hh:(debt F₀ j (j+n) V T B):=by
       intro i t; obtain ⟨hs,heq⟩:= Finset.mem_Ico.mp t; let S(i):= (F₀).coeffSize (W i); have hu:S i+ S (i+1)≤ (D+D)*L:=by rw [add_mul]; exact add_le_add ((capPrice P g u hp w) i (Finset.mem_Icc.mpr ⟨hs,heq.le⟩)) ((capPrice P g u hp w) (i+1) (Finset.mem_Icc.mpr ⟨by omega,heq⟩));
       rw [show V i-T i (V (i+1))= W i-T i (W (i+1)) by unfold V; rw [map_sub,ht i t]; abel]; exact (search_cost P u t _).trans ((mul_le_mul_of_nonneg_left hu u.cost).trans_eq (mul_assoc ..).symm)
    have hx:= (bound_ledger F₀ (TowerS d)).choose_spec Y u.y B hB j (j+n) (by omega) (by rw [Nat.add_sub_cancel_left]; exact u.bill) V T (ledger u) hh (j+n) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩); rw [show V (j+n)= w - chipAt C j (j+n) r • v from by unfold V W charges finalX; rw [LinearEquiv.apply_symm_apply] <;> rfl] at hx
    refine hx.trans (mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans (Credit.purchase _ u.y)))
    have hW:tollQ C d j p≥0:= mul_nonneg (invoice_nn _ _ _) (zero_le_one.trans (C.path.levels.params j|>.columns_ge))
    have hε: (F₀).coeffSize ( W j-A w) ≤ tollQ C d j p*(2*L):= (size_sub_rev F₀ _ _).trans_le ((P.yearn g hp w).trans (mul_le_mul_of_nonneg_left (P.gruesome g hp w) hW))
    unfold money; have hz: V j=W j- A w+(A w-v):= by unfold V R T' chipAt; rw [div_self (ne_of_gt (Hv j)),Complex.ofReal_one,one_pow,one_smul]; abel
    rw [hz]; exact (add_le_add_left ((Extra.Histories.Size.add ..).trans (add_le_add_left hε _)) B).trans_eq (by unfold B L D; ring)
-- Turning filing covariance. Exact same W/weight/rank, arbitrary accuracy edit invoice.
abbrev phasePollCost (F:Frame G d)(Y:ℝ):ℝ:= 4*orbitCost F*(pollS F Y)
lemma motionAt (v:C.label d)(s:Extra.Histories.Motion):
    (F₀).coeffSize (A.symm (Extra.Histories.Motion.patch F₀ s v)- Extra.Histories.Motion.patch F₀ s (A.symm v)) ≤ phasePollCost F₀ Y*(tollQ C d j p)* (F₀).coeffSize v:=by
    let e:= tollQ C d j p; let w:=(F₀).coeffSize v; have he:0 ≤ e:= mul_nonneg (invoice_nn _ _ _) (zero_le_one.trans (C.path.levels.params j|>.columns_ge)); have Hw:0 ≤ w:= size_nonneg ..
    let x:= A.symm v; let G(u):= Extra.Histories.Motion.patch F₀ s u; let k:= orbitCost F₀; have hk:0≤k:=zero_le_one.trans (orbitCost_one_le ..); have ht : (F₀).coeffSize (P.pollAt x) ≤ 2*w:=by let H:= gruesome P g hp x; unfold x at *; rw [LinearEquiv.apply_symm_apply] at H; exact H
    have hz : (F₀).coeffSize (P.pollAt (G x)) ≤ k*(2*w):=by unfold G; rw [P.phasePoll]; exact (patch_cost ..).trans (mul_le_mul_of_nonneg_left ht hk)
    have hy : (F₀).coeffSize (A (G x)-P.pollAt (G x))≤ e*(k*(2*w)):= (P.yearn g hp (G x)).trans (mul_le_mul_of_nonneg_left hz he)
    have hg : (F₀).coeffSize (G v-P.pollAt (G x)) ≤ k*(e*(2*w)):=by
       have hx(u v): G (u-v)=G u-G v:=by
          unfold G Extra.Histories.Motion.patch; rw [_root_.map_sub]; split; · rw [star_sub];
          rfl
       have hh: G v-P.pollAt (G x)=G (v-P.pollAt x):= by rw [hx,P.phasePoll] -- P.phasePoll match abbrev?
       rw [hh]; apply (patch_cost ..).trans; refine mul_le_mul_of_nonneg_left (le_trans ?_ (mul_le_mul_of_nonneg_left ht he)) hk; rw [←show A x=v from LinearEquiv.apply_symm_apply ..]; exact P.yearn g hp x
    let z:= G v-A (G x); have H': (F₀).coeffSize z≤4*k*e*w:= calc
          _ ≤ (F₀).coeffSize (G v-P.pollAt (G x))+(F₀).coeffSize (P.pollAt (G x)-A (G x)):=by unfold z; rw [show G v-A (G x)= (G v-P.pollAt (G x))+(P.pollAt (G x)- A (G x)) from by abel]; exact Extra.Histories.Size.add ..
          _ ≤ _ := le_trans (add_le_add hg ((size_sub_rev ..).trans_le hy)) (le_of_eq (by ring))
    change (F₀).coeffSize (A.symm (G v)- G x) ≤ _; rw [show A.symm (G v)-G x = A.symm z from by unfold z; rw [map_sub,LinearEquiv.symm_apply_apply]]; exact (worth P g u hp z).trans ((mul_le_mul_of_nonneg_left H' (by unfold pollS; positivity [Credit.purchase (chargeS F₀) u.y])).trans_eq (by unfold phasePollCost; unfold k w e; ring))
end PurchVoice
end YM.SignedWilsonExpansion.Purchases
