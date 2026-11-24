import YM.WilsonCoeffUV.Vacuum.Step.Subtract
/-!
# Real ranks follow-up gate. Inputs rescaled link homogeneous. Energy derivative
corrector = identity at unchanged grade before splitting logs. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{I:Gear G}{i j k r:ℕ}{E A B B' C s t σ: ℝ}
namespace Gear

def bill (T:Gear G)(r:ℕ) := tauV G r T.preB T.s T.past T.σ
lemma bill0 : 0≤ I.bill r := tauV_nn G r I.pre_nn I.depth I.holds
-- put rootpose normalization pre-weight.
def gain (T:Gear G)(r:ℕ):= T.bill r*ruby T.σ T.sig
lemma gain0 : 0≤ I.gain r:= mul_nonneg bill0 (zero_le_one.trans (ruby_nn I.price I.tag_nn))
-- wind shares pinned to strict loco

def twist (I:Gear G)(k r:ℕ):= postV G I.patch.L r I.preB I.D I.D I.s I.past I.σ *levyWind G I.past k (r+1)
lemma twist0 : 0≤ I.twist k r:= mul_nonneg (postV_nn G _ r I.pre_nn I.holds) (levyWind_nn ..)

def towing (I:Gear G)(r:ℕ): Prop:= ((r+2:ℕ):ℝ)*I.s/I.patch.L.val ≤ I.past/2
end Gear

namespace Stand
def zenith (M:Stand I) (k r:ℕ): Ten ℝ (YForest G) r := prism M.Q (plants I.patch.L (M.page k)) r
def dawnR (M:Stand I)(k r:ℕ): Ten ℝ (YForest G) r:= M.corr k r + retent (orbQ M.Z) (- M.flashback r k)

lemma calcit (M:Stand I){r k}{C B:ℝ}(h: Amber terrain I.past C (M.page (k+1) (r+2)))(e:I.towing r)
    (p: ∀ i< k+1,∀ j≤r+2, Amber terrain I.past B (M.page i j))(q:0≤B)(b:dragCup terrain I.s I.D M.Q): Amber terrain I.σ
    (I.bill r*C /I.patch.L.val + I.twist (k+1) r*B) (M.zenith (k+1) (r+2)) := by
    have hp := draft_due M.even_page M.sym p I.depth.le q
    have H : r+1+1=r+2:=rfl
    rw [Gear.twist,mul_assoc (postV ..)]; exact platinum M.crank M.rule b M.rolls (M.sym _ _) h hp (M.bit _ (by positivity)) (M.move _ _) I.price.le I.holds I.depth e
lemma shake_post (P:Stand I)(k r){C E:ℝ}(h: Amber terrain I.σ C (P.flashback (r+2) (k+1)))(g:Amber terrain I.σ E (P.zenith (k+1) (r+2))) :
    P.stake (k+1) (r+2)=retent (orbQ P.Z) (P.zenith (k+1) (r+2))+P.dawnR (k+1) (r+2):=by
  rw [P.component (by omega),P.post k r]; unfold zenith at g ⊢; rw [retent_add _ h.neg g I.price]; unfold dawnR; abel
end Stand
lemma early_stripe (e r:ℕ): Satin (largus e r) (smallus e r (G:=G)) Gear.σ (fun _ x=>x.P.dawnR e r) (fun _ x=>x.Q.dawnR e r):=by
   have hp : Satin (largus e r (G:=G)) (smallus e r) Gear.σ (fun _ x=>x.P.corr e r) (fun _ x=>x.Q.corr e r):=by
      unfold Stand.corr; apply Satin.sum (fun i=>permits i e r); intro j hj
      obtain ⟨hh,hv⟩:= Finset.mem_erase.mp hj; have he:= Finset.mem_range.mp hv
      let H:= Satin.delta_full (show lowerGrade j r e r from Or.inl he) (G:=G)
      exact Satin.μ (titles (i:=e-j) (G:=G) (by omega) r j r) (Satin.closure H)
   have h:=Satin.closure (note_partial (G:=G) e r).neg; exact hp.add h (fun i=>permits i e r)

-- exact continuity in x while keeping contracted rank.
section gaps
variable {Q R:Ten ℝ (YForest G) 2}
lemma clothAware (h:Amber terrain s A Q)(e:Amber terrain s E R)(hs:0<s)(p:Aware Q)(u:Aware R): Aware (Q-R):=by
   have he (i j k f)(a:broad f): tailor (Q-R) i j k f=tailor Q i j k f-tailor R i j k f:=by
      unfold tailor petals; simp_rw [Pi.sub_apply,mul_sub]; exact (tailor_sum h hs _ _ _ _ a).tsum_sub (tailor_sum e hs _ _ _ _ a)
   intro i v c
   refine ⟨?_,fun j=>?_,fun j k=>?_⟩
   · rw [he _ _ _ _ broad.one,(p ..).1,(u ..).1,sub_zero]
   · rw [he _ _ _ _ (broad.chalk _),(p ..).2.1 j,(u ..).2.1 j,sub_zero]
   rw [he _ _ _ _ ((broad.chalk _).mul (broad.chalk _)), (p ..).2.2 j k,(u ..).2.2 j k,sub_zero]

private lemma subtract_col {L:Side}{P Q: Gen ℝ (YForest G)}(M: ropes Cover (Co L (Hooks G)) (Hooks G)){s t C:ℝ}{r:ℕ}(h:Amber terrain t B (P (r+2)))(g:Amber terrain t B (Q (r+2)))(he:dragCup terrain s C M)(hp:0<s) (hv:s/L.val≤t):
    prism M (plants L (P-Q)) (r+2) = prism M (plants L P) (r+2)- prism M (plants L Q) (r+2):=by
    simp_rw [lead_pump];
    funext x; simp only [Pi.sub_apply,Bank.pump]; rw [← ((pump_sum (fun i=> ownS (r:=r+2) he i) h hp hv x).of_norm.tsum_sub ((pump_sum (fun i=> ownS (r:=r+2) he i) g hp hv x).of_norm))]; exact tsum_congr fun y=> by simp [spinJob,mul_sub]
end gaps

variable (R : Rally (k+1) (r+2) I)
lemma tempestic (h: Amber terrain I.past B (R.P.page (k+1) (r+2))) (g: Amber terrain I.past B (R.Q.page (k+1) (r+2))) (q: Amber terrain I.past E (R.P.page (k+1) (r+2) - R.Q.page (k+1) (r+2))) (ht: I.towing r) :
   Amber terrain I.σ (I.bill r * E / I.patch.L.val + I.twist (k+1) r*(R.x*R.σ))
       (prism R.P.Q (plants I.patch.L (R.P.page (k+1))) (r+2)-prism R.P.Q (plants I.patch.L (R.Q.page (k+1))) (r+2)) := by
    let X:= R.P.page-R.Q.page; let Y:= X (k+1)
    have he z: Pure (X z):= Pure.sub (R.P.sym z) (R.Q.sym z)
    have hz : stroll (Y (r+2)):= by intro b x; unfold Y X; simp only [Pi.sub_apply,R.P.move _ _ b _, R.Q.move _ _ b _]
    have hl : Draft (Y (r+2)) I.past (levyWind G I.past (k+1) (r+1)*(R.x*R.σ)):= draft_due (vertical_pair R.P.even_page R.Q.even_page) he (fun i hi j _=> (R.paid i j (Or.inl hi)).visit) I.depth.le (mul_nonneg (zero_le_one.trans R.rich) R.θ)
    rw [← subtract_col (G:=G) R.P.Q h g R.Υ.oneP (lt_trans I.price I.holds) I.room];
    change Amber _ _ _ (prism R.P.Q (plants I.patch.L Y) _)
    rw [Gear.twist, mul_assoc (postV ..)]
    -- adjust Q-P where not rank r+2 so AxisClear premise trivial
    by_cases H:r=0
    · subst r; have hv : AxisClear Y:= clothAware h g I.depth (R.P.bit _ (by positivity)) (R.Q.bit _ (by positivity)); exact platinum R.P.crank R.P.rule R.Υ.oneP R.P.rolls (he _ _) (P:=Y) q hl hv hz I.price.le I.holds I.depth ht
    let U: Gen ℝ (YForest G):= shine (Y (r+2))
    have hh: U (r+2)=Y (r+2):= shine_lit _
    have hg : prism R.P.Q (plants I.patch.L Y) (r+2)=prism R.P.Q (plants I.patch.L U) (r+2):= by simp only [prism, plant_pt,tiles,Bank.bend, hh]
    rw [hg];
    have hf:AxisClear U:= by unfold AxisClear; rw [show U 2=0 from shine_dark (by omega)]; intro i v c; simp [tailor,petals]
    refine platinum R.P.crank R.P.rule R.Υ.oneP R.P.rolls ?_ ?_ ?_ hf ?_ I.price.le I.holds I.depth ht
    · rw [hh]; exact he (k+1) _
    · rw [hh]; exact q
    · rw [hh]; exact hl
    rw [hh]; exact hz

-- post bill for switches charge from difference and magnitude.
def barrel (I:Gear G)(r:ℕ) := ((r+2+1:ℕ):ℝ)*I.D^(r+2)*(Fintype.card (Site I.patch.L)*Real.exp (8*I.s))*tieN (Co I.patch.L (Hooks G)) (I.s-I.σ) (r+2)
lemma barrel_nn (I:Gear G)(r:ℕ):0≤ barrel I r:= by
    unfold barrel; have hp:0≤I.D:= zero_le_one.trans I.bill_nn; exact mul_nonneg (by positivity) (tieN_nn (sub_pos.mpr I.holds) _)
lemma nozzle (R:Rally (k+1) (r+2) I) (h: Amber terrain I.past B (R.Q.page (k+1) (r+2))) : Amber terrain I.σ (barrel I r*B*R.σ) (prism R.P.Q (plants I.patch.L (R.Q.page (k+1))) (r+2)-R.Q.zenith (k+1) (r+2)):=by
  let H:= PairA.prune_bill R.Υ R.θ I.holds I.price.le (PairA.pack (P:=R.Q.page (k+1)) (Q:=R.Q.page (k+1)) (PairA.echo h R.θ) (lt_trans I.price I.holds).le I.room); apply H.visit.le; exact le_of_eq (by unfold barrel; ring)
lemma turningC (R:Rally (k+1) (r+2) I)(h: Amber terrain I.past B (R.P.page (k+1) (r+2)))(p:Amber terrain I.past B (R.Q.page (k+1) (r+2)))(q:Amber terrain I.past C (R.P.page (k+1) (r+2)-R.Q.page (k+1) (r+2)))(ht:I.towing r):
    let y:=I.bill r*B/I.patch.L.val+I.twist (k+1) r*R.x
    let W:= R.P.zenith (k+1) (r+2); let V:= R.Q.zenith (k+1) (r+2)
    Amber terrain I.σ y W∧ Amber terrain I.σ y V∧ Amber terrain I.σ (I.bill r*C/I.patch.L.val + I.twist (k+1) r*(R.x*R.σ)+barrel I r * B*R.σ) (W-V):=by
   intro y W V
   refine ⟨Stand.calcit _ h ht (fun i hi j _=>(R.paid _ _ (Or.inl hi)).pose) (zero_le_one.trans R.rich) R.Υ.oneP, Stand.calcit _ p ht (fun i hi j _=>(R.paid _ _ (Or.inl hi)).vale) (zero_le_one.trans R.rich) R.Υ.otherP,?_⟩
   have hp:= (tempestic R h p q ht).add (nozzle R p)
   rw [sub_add_sub_cancel] at hp; exact hp
end YM.WilsonCoeffUV.Bank
