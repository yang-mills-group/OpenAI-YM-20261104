import YM.LocalLTE.River.Pulp
/-!
# Conservation under charged camera pans/Bar

Use only the actual lay of lands. For probing the resulting exhibition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.River
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox FrameBox.Hall AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom Motion
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n κ:Side}{p:BudgetPoint}{d:ℕ}{F:Labels.Frame G d}{A:Hol G}{D:SectionData F}{R:Rep G n}{k v a u u' s t e x y z:ℝ}{m ℓ j:ℕ}{i:Site n}
local notation "Xp"=> Config G n→ℂ
open Next.Foundations Push.AbsoluteSums Animals
variable {L:Support n}
set_option quotPrecheck false
variable (r:Extra.Histories.Motion)(S:R.activities.Moves r.1 0)
local notation "q"=> turnSites r.1 (0:Site n)
local notation "rp"=> rotationP F R.p.order R.p.power
local notation "P'" P=> audition (z:=r) S P
variable {P Q:Coefficient F n}

-- A ladder rung must donate the increment, including the certified model
-- part in the readback row, not merely a regular mismatch estimate.
lemma offFormat (hP:P.Format 0 A R) (hQ:Q.Format 0 A R)(hf:Q.forced=0)(hL:P.support=Q.support): (Vinca.decrement P Q).Format 0 A R:=by
   have hD : (Vinca.decrement P Q).forced=P.forced:=by unfold Vinca.decrement; rw [hf,sub_zero]
   have hp l: Reads A 0 (P.support l) (0:Label G d) ((Vinca.decrement P Q).regular l):=by -- null Reading.
       have hA : Reads A 0 (P.support l) (0: Label G d) (Q.regular l):=by rw [hL];exact (Next.Foundations.reads_null_iff ..).2 ⟨hQ.identity_null _,hQ.projects _⟩
       have ht : Reads A 0 (P.support l) (0: Label G d) (P.regular l):= (Next.Foundations.reads_null_iff ..).2 ⟨hP.identity_null _,hP.projects _⟩
       have he:= Next.Foundations.reads_sub ht hA; rw [sub_zero] at he; exact he
   refine ⟨fun i=>?_, hP.origin, fun i=> (Next.Foundations.reads_null_iff ..|>.mp (hp i)).1, fun i=> (Next.Foundations.reads_null_iff ..|>.mp (hp i)).2,hD.symm ▸ hP.forcing,hD.symm ▸ hP.carried,hD.symm ▸ hP.invariant,hD.symm ▸ hP.supported,hD.symm ▸ hP.borel⟩
   exact Next.Foundations.regular_sub (hP.smooth i) (hL.symm ▸ hQ.smooth i)

lemma quietCredit : Patrons D k ℓ m p (Vinca.decrement P P) 0 :=by
   apply River.patronC _ _ _
   · simp [Vinca.decrement,Frame.coeffSize]
   · simp [Vinca.decrement]
   simp [Vinca.decrement]
lemma appraise (h:Patrons D k ℓ m R.p Q t)(hp: Q.Format 0 A R)(hs:0<s):Exhibition D k ℓ m A R Q Q s t 0:=by
   have he:= quietCredit (k:=k) (D:=D) (ℓ:=ℓ) (m:=m) (P:=Q) (p:=R.p); exact ⟨h,hp,rfl,offFormat hp hp h.forced rfl, he.bill hs,he.principal⟩
lemma takes (h:Patrons D k ℓ m R.p P t)(hp:P.Format 0 A R)(hD:D.Sound A)(hk:ConnectedActivityE6.Reliable G k v)(hs:0<s)(hn: 2 ≤ n.val): Patrons D k ℓ m R.p (P' P) ((rotationP F R.p.order R.p.power)*t):= (River.pitch r S (appraise h hp hs) hD hk hn).stock
variable {ι:Type*}[Countable ι](L0:ℕ ≃ ι×ℕ)
lemma remounted (X Y:ι→ Coefficient F n) {t s e:ι→ℝ}{u:ℝ}(hu:0<u)(hX:∀ i,(X i).Format 0 A R)(hY:∀ i,(Y i).Format 0 A R)(h:∀ i,(X i).support=(Y i).support) (hP:∀ i,Patrons D k ℓ m R.p (X i) (t i)) (hp:∀ i, Patrons D k ℓ m R.p (Y i) (s i)) (he:∀ i, Patrons D k ℓ m R.p (Vinca.decrement (X i) (Y i)) (e i))(hs:Summable t)(hz:Summable s)(hW:Summable e) : Patrons D k ℓ m R.p (Vinca.decrement (Extra.Histories.merge L0 X) (Extra.Histories.merge L0 Y)) (∑' i,e i):=by
    let f i:= Vinca.decrement (X i) (Y i)
    have hf i: (f i).Format 0 A R:= River.offFormat (hX i) (hY i) (hp i|>.forced) (h i)
    have hQ (i):=(hp i).forced; have ht:= hs.of_nonneg_of_le (fun i=> Work.G08.size_nonneg F ((X i).x)) (fun i=> hP i|>.principal); have hs:= hz.of_nonneg_of_le (fun i=> Work.G08.size_nonneg F ((Y i).x)) (fun i=> hp i|>.principal)
    let Q:= Extra.Histories.merge (n:=n) (F:=F) L0; have hZ: Vinca.decrement (Q X) (Q Y)=Q f:=by
        unfold Vinca.decrement Q f; simp only [Extra.Histories.merge, decrement]; congr 1
        · exact Eq.symm ((Size.series F ht|>.of_norm).tsum_sub (Size.series F hs|>.of_norm))
        funext i v; simp only [Pi.sub_apply,hQ,Pi.zero_apply,tsum_zero,sub_zero]
    change Patrons _ _ _ _ _ (Vinca.decrement (Q X) (Q Y)) _; rw [hZ]; exact (River.auctions L0 f f (fun i=> appraise (he i) (hf i) hu) hW summable_zero hu).stock
end YM.LocalLTE.River
