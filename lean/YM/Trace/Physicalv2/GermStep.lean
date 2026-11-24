import YM.Trace.Physicalv2.GermGraph
/-! One step on the *same* representations. The correction to the ordinary
coordinate test is a wrapping price; old labels need not match the new labels
at this step. We keep exact identities of densities, so no differentiation of
near-zero conditional denominators. This is the stable-error recursion for a
single marked trajectory; the local map on analytic short packets and the
mixed-marker stop remain separate estimates. -/
noncomputable section
namespace YM.Trace.Physical.GermGraph
open Function Set Filter Labels Lattice Wilson RG Source Analysis Next.Foundations
open Push.Local ProjectorNext.Equivariance MeasureTheory Extra.Histories Relay
open Germ Bid Work.G08 PhysicalNext.Repeat.Lotus YM.MergeProof Motion
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 125000
set_option quotPrecheck false
set_option warningAsError false
set_option maxRecDepth 3600
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
variable {G:Gauge}{C:Family G}(d:ℕ)(N p m:ℕ)
local notation "F" => C.labels.level d
local notation "Iy" => C.factory d N p
local notation "R₀" => C.path.rep N p
local notation "ent" => (C.factory d N p).entries
local notation "cnt" => (C.labels.level d).coeffSize
local notation "inv'" => invoice (C:=C) d
local notation "B" => C.localSection d
abbrev value(i:ℕ)(q:Coefficient F (C.side i p)):=q.density 0 B (R₀ i)
def calValues(i:ℕ)(x:C.label d):= value d N p i (ent i x)
-- m dummy? don't include m by default unless notation
noncomputable def transition(i)(f:Config G (C.side (i+1) p) → ℂ):Config G (C.side i p) →ℂ := blast C.path N p i d f
abbrev qsumP(i:ℕ) := page (C:=C) d p i
lemma rem_increase {n:Side}{R:Rep G n}{F':Frame G d}{q:Coefficient F' n}{a b κ:ℝ}{o:Site n}(hq:q.remBound o R κ a)(he:a≤b):q.remBound o R κ b:=by obtain ⟨e,f,he',hf,hab,H⟩:=hq; exact ⟨e,f,he',hf,hab.trans he,H⟩
lemma message (i:ℕ)(H:C.Makes)(hp : C.ref d ≤ i)(hi:i ≤ N){q:Coefficient F (C.side i p)}{r:ℝ}(h: reads d N p i q r) : Integrable (value d N p i q) (prior G (C.side i p)):= play_integrable C.path N H.wilson hi h.1 h.2
private lemma plus_value (i)(k v:Coefficient F (C.side i p)){r t:ℝ}(H:C.Makes)(hi:i ≤ N)(hq:reads d N p i k r)(hv: reads d N p i v t): value d N p i (beside k v)=value d N p i k+value d N p i v := plus (H.wilson.represents _ _ _ hi|>.good) hq.2 hv.2 B
lemma transition_add {i:ℕ} {u v:Config G (C.side (i+1) p)→ℂ}(hu:Integrable u (prior G _))(hv:Integrable v (prior G _)): transition (C:=C) d N p i (u+v) = transition d N p i u + transition d N p i v := by unfold transition blast; rw [StepData.push_add (C.path.levels.transition_mass i p _) _ _ hu hv,smul_add]
include N in
lemma factory_eq (i:ℕ)(H:C.Makes)(hp : C.ref d ≤ i)(hi:i < N)(x:C.label d): calValues d N p i x = transition d N p i (calValues d N p (i+1) x):= (H.calibrated d N p (hp.trans hi.le)).unnormalized i hp hi x
lemma cal_add (i:ℕ)(H:C.Makes)(hp : C.ref d ≤ i)(hi:i ≤ N)(x y:C.label d): calValues d N p i (x+y)= calValues d N p i x+calValues d N p i y :=by
   induction hi using Nat.decreasingInduction with
   | self =>
     have hval(v u):= (H.calibrated d N p hp).encode v u
     ext u
     unfold calValues value
     simp only [Pi.add_apply]; rw [hval,hval,hval]; unfold initial; simp only [map_add,Pi.smul_apply, SectionData.places, (C.localSection d).eval_linear.map_add,smul_eq_mul,Pi.add_apply]; ring
   | of_succ i hi ih =>
     have he:= hp.trans i.le_succ
     rw [factory_eq d N p i H hp hi (x+y), ih he, transition_add d N p (u:=calValues d N p (i+1) x) (v:=calValues d N p (i+1) y) (message d N p _ H he hi (entryOk d N p _ H he hi x)) (message d N p _ H he hi (entryOk d N p _ H he hi y)), ← factory_eq d N p i H hp hi x, ←factory_eq d N p i H hp hi y]

def startLoss (C:Family G)(d p m:ℕ) := (stock C (m+1))*(invoice d (m+1) p (C:=C))
def coordLoss (C:Family G)(d p m:ℕ)(η:ℝ) := (1+invoice (C:=C) d m p)*η*(1+startLoss C d p m)
def stableLoss (C:Family G)(d p m:ℕ)(η:ℝ) := η*(1+startLoss C d p m)+2*(stock C m)*coordLoss C d p m η
def feedLoss (C:Family G)(d p m:ℕ)(η:ℝ) := coordLoss C d p m η + 2*(stock C (m+1))*(factor C m ^d) * invoice (C:=C) d (m+1) p

private lemma rem_nn {n:Side}{F':Frame G d}{R:Rep G n}{r κ:ℝ}{o:Site n}{q:Coefficient F' n}(h:q.remBound o R κ r) : 0 ≤ r :=by obtain ⟨a,b,ha,hb,hab,-⟩:=h; linarith
lemma invoice_nn : 0 ≤ invoice (C:=C) d m p := by
    unfold invoice price cut
    have he:= (germ_close (F) C.params).choose_spec.1
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) he.le) (show 0≤Germ.wraps _ _ from (Real.exp_pos _).le)
lemma smaller {i:ℕ}(ho:Opened C d i p): invoice (C:=C) d i p ≤ 1/4:= (le_mul_of_one_le_right (invoice_nn ..) (stage C _|>.columns_ge)).trans ho.small.le
private lemma size_change (x y : C.label d) : cnt x ≤ cnt y+cnt (x-y) := by simpa only [add_sub_cancel] using Size.add F y (x-y)
lemma zero_cal(i:ℕ)(H:C.Makes)(hp : C.ref d ≤ i)(hi:i ≤ N):calValues (C:=C) d N p i 0=0:=by
   have h0 : (0:C.label d) + 0=0:=zero_add _
   have hz:=cal_add d N p i H hp hi (0:C.label d) 0
   rw [h0] at hz; exact add_left_cancel (a:=calValues d N p i 0) (hz.symm.trans (add_zero _).symm) -- wrong

lemma addPage (i)(k v:Coefficient F (C.side i p)){r t:ℝ}(H:C.Makes)(hp : C.ref d ≤ i)(hi:i ≤ N)(hq:reads d N p i k r)(hv: reads d N p i v t): page d p i (beside k v)=page d p i k+page d p i v := by
   have hs: (R₀ i).p= _:= (H.wilson.represents _ _ _ hi).vac
   simpa only [page,hs] using add_projection d k v hq.1 hv.1 (dimensions d N p i H hp hi).1 (dimensions d N p i H hp hi).2 ⟨_,_,hq.2⟩ ⟨_,_,hv.2⟩
lemma transfer_cost (H:C.Makes)(hm:m<N)(h:Opened C d m p) (ho:Opened C d (m+1) p)(y:C.label d):
    cnt (fitting d N p (m+1) H ho hm y) ≤ 4*(stock C (m+1)) * cnt (fitting d N p m H h hm.le y) :=by
    have k:=H.calibrated d N p (h.post.trans hm.le)
    have hu:= k.back m h.post hm y
    have hL:= (size_gap d N p (m+1) H ho hm y).1.trans (mul_le_mul_of_nonneg_left hu zero_le_two)
    let fee:=fitting d N p m H h hm.le
    let c:=stock C (m+1)
    have hx:=mul_le_mul_of_nonneg_left (size_gap d N p m H h hm.le y).2 (show 0 ≤ 2*c from mul_nonneg zero_le_two (zero_le_one.trans (stage C _|>.columns_ge)))
    change 2*c*cnt ((ent m y).x) ≤ (2*c) * (2*cnt (fee y)) at hx
    change cnt (fitting d N p (m+1) H ho hm y) ≤ 2*(c*cnt ((ent m y).x)) at hL
    exact le_trans hL (by linarith only [hx])

lemma stable_step (H:C.Makes) {t η:ℝ} {D : GaugeDoor (R₀ (m+1)) (R₀ m)}(hm:m<N)(hp : Opened C d m p)(hfine:Opened C d (m+1) p)
      (hu : Tones B C.path N p C.params t m η D) (q : Coefficient F (C.side (m+1) p)) {r:ℝ} (hq: reads d N p (m+1) q r)(hν: page d p (m+1) q=0):
    ∃ (v:Coefficient F (C.side m p)) (y:C.label d), reads d N p m v (stableLoss C d p m η*r) ∧ page d p m v=0 ∧ cnt (fitting d N p m H hp hm.le y) ≤ feedLoss C d p m η * r ∧ transition d N p m (value d N p (m+1) q)= value d N p m v + calValues d N p m y := by
    have h0η:=hu.tuned.2.2.2
    -- split raw primary, not transported alone without its true library column
    let x:= MultiNext.SignedSource.fits H hfine.post hm p q.x
    let neg:=ent (m+1) (-x)
    let z:= (invoice (C:=C) d (m+1) p)*r
    have hb:= hfine.post
    have hfit(v : C.label d) : (ent (m+1) (MultiNext.SignedSource.fits H hb hm p v)).x=v := (MultiNext.SignedSource.matrices H hb hm p).apply_symm_apply v
    have hx : (ent (m+1) x).x=q.x := hfit q.x
    have hM := (H.calibrated d N p (hb.trans hm)).linear _ hb hm
    have hn : neg.x = -(ent (m+1) x).x:= (hM.1.mk' _).map_neg x
    have hw:cnt neg.x ≤ z := by
        have he := measured_diff d N p (m+1) H hb hm hq; rw [hν,zero_sub] at he
        simpa only [hn,hx,Frame.coeffSize,Pi.neg_apply,norm_neg] using he
    let u:=beside q neg
    let a:= (1+startLoss C d p m)*r
    have hs : (ent (m+1) x).x = q.x:= hx
    have hcx : cnt ((ent (m+1) x).x) ≤ z := by simpa only [hn,Frame.coeffSize,Pi.neg_apply,norm_neg] using hw
    have hu0 : u.x=0:= by rw [show u.x=_ from reckon q neg,hn,hs,add_neg_cancel]
    have ht := entryOk d N p (m+1) H hb hm (-x)
    obtain ⟨hUF,hUR⟩:=presentation hq.1 hq.2 ht.1 ht.2
    have hcharge : u.remBound 0 (R₀ (m+1)) (safety C (m+1)) a:=rem_increase d hUR ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hw (zero_le_one.trans (stage C (m+1)|>.columns_ge)))).trans_eq (?_:_=a))
    swap; unfold a z startLoss; ring
    have ha:= rem_nn d hcharge; have hvac:0≤ η*a:=mul_nonneg h0η ha
    have hv:= plus_value d N p (m+1) q neg H hm hq ht
    obtain ⟨X,hX,htone⟩:=hu.priced
    obtain ⟨s,hPs,hSet⟩:=htone u a hu0 hUF hcharge
    have hread : reads d N p m s (η*a):=⟨hPs.format,hPs.bound⟩
    let Qs := fitting d N p m H hp hm.le
    let l:= Qs.symm (page d p m s)
    have hl : Qs l=page d p m s:= Qs.apply_symm_apply _
    have hS : cnt s.x≤η*a:=(le_mul_of_one_le_left (size_nonneg ..) (orbitCost_one_le _)).trans (sub_zero s.x ▸ hPs.leadP)
    have hg:= graph_cost d N p m H hp hm.le (-l)
    have hk:cnt (Qs (-l))=cnt (Qs l):=by rw [map_neg]; simp [Frame.coeffSize]
    have hl₁ : cnt (Qs l) ≤ coordLoss C d p m η*r:= by
       refine hl ▸ (size_change d _ s.x).trans ((add_le_add hS (measured_diff d N p m H hp.post hm.le hread)).trans_eq ?_)
       unfold coordLoss a;ring
    let s' := beside s (ent m (-l))
    have hx':cnt (Qs x) ≤ 2*(stock C (m+1)*factor C m^d*z):=by
       exact (size_gap d N p m H hp hm.le x).1.trans (mul_le_mul_of_nonneg_left (((H.calibrated d N p (hp.post.trans hm.le)).front _ hp.post hm x).trans (mul_le_mul_of_nonneg_left hcx (mul_nonneg (zero_le_one.trans (stage C (m+1)|>.columns_ge)) (by unfold factor; positivity):0 ≤ stock C (m+1)*factor C m^d))) zero_le_two)
    obtain ⟨hU',hB⟩:=presentation hread.1 hread.2 hg.1 hg.2
    refine ⟨s',x+l,?_,?_,?_,?_⟩
    · have hk': cnt ((fitting d N p m H hp hm.le) (-l)) ≤ _:= hk.trans_le hl₁
      refine ⟨hU',rem_increase d hB ((add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hk' (show 0≤2*stock C m from mul_nonneg zero_le_two (zero_le_one.trans (stage C _|>.columns_ge))))).trans_eq ?_)⟩
      unfold stableLoss a
      ring
    · rw [show page d p m s' =_ from addPage d N p m s (ent m (-l)) H hp.post hm.le hread hg]; change page d p m s+Qs (-l) = 0; rw [map_neg,hl,add_neg_cancel]
    · change cnt (Qs (x+l)) ≤ _;rw [map_add]; unfold feedLoss; rw [add_mul]; unfold z at hx'; apply le_trans (Size.add ..); linarith only [hx',hl₁]
    have hr:=hPs.agrees
    change value d N p m s=transition d N p m (value d N p (m+1) u) at hr
    rw [hv,transition_add d N p (message d N p (m+1) H hb hm hq) (message d N p (m+1) H hb hm ht)] at hr
    have hhandler := plus_value d N p m s (ent m (-l)) H hm.le hread hg
    rw [show value d N p m s' = _ from hhandler, cal_add d N p m H hp.post hm.le]
    change _= value d N p m s+calValues d N p m (-l)+(calValues d N p m x+calValues d N p m l)
    change value d N p m s = transition _ _ _ _ (value d N p (m+1) q) + transition _ _ _ _ (calValues d N p (m+1) (-x)) at hr
    rw [←factory_eq d N p m H hp.post hm (-x), show calValues d N p m (-x) =- calValues d N p m x from ?_] at hr
    rw [hr,show calValues d N p m (-l) = - calValues d N p m l from ?_]; abel
    all_goals -- negative via add
       apply eq_neg_of_add_eq_zero_left
       rw [← cal_add d N p m H hp.post hm.le,neg_add_cancel,zero_cal d N p m H hp.post hm.le]
end YM.Trace.Physical.GermGraph
