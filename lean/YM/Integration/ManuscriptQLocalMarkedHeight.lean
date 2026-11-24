import YM.Integration.ManuscriptQLocalHeightPaidRows
import YM.Integration.QLocalRequestedSectorSale
import YM.LocalLTE.Marked.Post
import YM.LocalLTE.Quartz.Banner
import YM.LocalLTE.E6.Tickets

/-! All marked wings on the actual nonlinear inlet, including genuine compulsory
partners. The original local height charges each entire molecule. Only the
distinguished source labels use a temporary external radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkedHeight
open Function Filter Lattice RG Tree Pressure Pressure.Stores ConnectedActivityE6
open Push Push.AbsoluteSums Push.SectorMeasure AnalyticBridge VerifiedReset
open PhysicalNext PhysicalNext.Repeat Next.Scheduling Supply Input Testing
open Extra.Multi GridApprox.Nil MergeProof MergeProof.Menu
open Marker ConnectedActivityE6.Blaze Blaze.March Silica Clutch SliceRows RG.Shoot
open LocalLTE Height Captain Daisy Charity
open scoped Classical Topology BigOperators

variable {G:Gauge}

def Booked (j n ℓ:ℕ) (P:Teller G) (Q:ConnectedActivityE6.Target G P) (E:Q.Expense)
    (L:Side) (W μ:ℝ) (o:Target.Order G W) (_:Stage) (_:ℕ) (x:ℝ) : Prop :=
  1≤betaF G x L ∧
  Height.grow G L x^ℓ≤Real.exp (Q.mark L μ x) ∧
  Height.grow G L x^ℓ≤Real.exp (Q.ε*Pressure.Stores.till x) ∧
  ∃v a:ℝ,|v⁻¹|≤betaF G x L ∧ a≤1 ∧
    Height.BorrowFundedRows P E j n ℓ Chi.canonical o L μ x v a

/-- A true chronological acquisition of the original marked Captain and the
two exceptional tests on the same Cash. All three clocks precede the field. -/
def decal (G:Gauge) (j n ℓ:ℕ) : Daisy.Charity.RG12.Decal G where
  rub:=Booked j n ℓ
  good P Q E:=by
    by_cases h0:E.wanting≤-(7/16:ℝ)
    · have hR:Q.rate < -(3/8:ℝ):=by linarith [E.reach]
      obtain ⟨M,hM⟩:=Height.canariesFundedRows P Q E hR
      refine ⟨M,fun L hL W μ o _ _ _ hW hμ=>?_⟩
      obtain ⟨v,a,hv,ha,h⟩:=hM L hL W μ o hW hμ j n ℓ Chi.canonical
      filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1,
        Height.byline ℓ E L hμ,hv 1 (by norm_num),ha 0 (by linarith),h]
        with x hβ hc hvx hax hx
      exact ⟨hβ,hc.1,hc.2,v x,a x,by simpa only [Real.rpow_one] using hvx,
        (le_abs_self _).trans (by simpa only [Real.rpow_zero] using hax),hx⟩
    · exact ⟨0,fun _ _ _ _ _ _ _ he _ _=>False.elim (h0 he)⟩

section Inputs
variable {c f:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f}

theorem pumps {b:ℝ} (h:R.activities.EBound R.p b) :
    Raw.Pumps R (fun _=>1) (1*b) := by
  obtain ⟨u,hu,hs⟩:=h
  exact ⟨fun _=>le_rfl,u,hu,fun y=>by simpa only [one_mul] using hs y⟩

variable {V ι:Type} [DecidableEq V] [Fintype V] [Fintype ι] {Γ:Census V}

theorem total (o:V→Site f) (M:ι→Menu.Hat Γ R) (w:V→ℝ) (hw:∀v,0<w v) {b:ℝ}
    (H:Menu.Offer o M w R.p.B R.p.supportExponent b) :
    (∑i,Menu.sumFee (M i) w*R.p.mass (M i).M.crest (M i).M.weight)≤
      (Fintype.card V:ℝ)*b := by
  let e (i:ι):=Menu.sumFee (M i) w*R.p.mass (M i).M.crest (M i).M.weight
  have pos i:0≤e i:=by
    unfold e RG.BudgetPoint.mass
    exact mul_nonneg (Menu.timed _ hw) (mul_nonneg (Real.exp_pos _).le (M i).M.profit)
  have pinned (v:V):(∑i,if o v∈(M i).M.crest then e i else 0)≤b := by
    have h:=budget_sum (H.budget (o v)) Finset.univ
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    all_goals simp only [e,Menu.fare,RG.BudgetPoint.mass]
    all_goals ring
  have each (i:ι):e i≤∑v:V,if o v∈(M i).M.crest then e i else 0 := by
    obtain ⟨v,hv⟩:=(M i).shiny
    have mem:=H.sites i (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    simpa only [if_pos mem] using
      (Finset.single_le_sum (f:=fun v:V=>if o v∈(M i).M.crest then e i else 0)
        (fun _ _=>by split <;> first | exact pos i | exact le_rfl) (Finset.mem_univ v))
  calc
    _ ≤ ∑i:ι,∑v:V,if o v∈(M i).M.crest then e i else 0 :=
      Finset.sum_le_sum fun i _=>each i
    _ = ∑v:V,∑i:ι,if o v∈(M i).M.crest then e i else 0 :=Finset.sum_comm
    _ ≤ ∑_:V,b:=Finset.sum_le_sum fun v _=>pinned v
    _ = _:=by simp [nsmul_eq_mul]

end Inputs

section Source
variable {P:Teller G} {Q:ConnectedActivityE6.Target G P} {E:Q.Expense}
  {c f:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f} {L:Side} {x W μ C:ℝ}
  {o:Target.Order G W} {j n ℓ:ℕ}

theorem one_mark {ι:Type} (M:ι→Lotus.Leaf R) (r:ι→ℝ) (hr:∀i,0≤r i)
    (hβ:1≤betaF G x L) (i:ι) :
    Height.mcount (S:=S) (G:=G) (L:=L) (s:=x) M r (fun _=>1) ℓ i ≤
      Height.grow G L x*r i := by
  have hg:1≤Height.grow G L x:=Real.one_le_rpow hβ (by norm_num)
  cases h:(M i).turn with
  | gasKey u =>
    simpa [Height.mcount,Merge.Palette.sign,h,Lotus.Wing.badge,Height.hip,
      Silica.lip,Silica.hornN] using le_mul_of_one_le_left (hr i) hg
  | logKey u =>
    simp [Height.mcount,Merge.Palette.sign,h,Lotus.Wing.badge,Height.hip,Silica.lip,
      Silica.hornN,Clutch.teethN,Raw.chargeN,Clutch.whip,Raw.wool]

theorem discounted {V ι:Type} [DecidableEq V] [Fintype V] [Fintype ι] {Γ:Census V}
    (M:ι→Menu.Hat Γ R) (origin:V→Site f) (w:V→ℝ) (hw:∀v,0<w v) {b:ℝ}
    (h:Menu.Offer origin M w R.p.B R.p.supportExponent b) (hβ:1≤betaF G x L)
    (hb:(Fintype.card V:ℝ)*b≤betaF G x L) :
    let β:=betaF G x L
    let A:=fun i=>β^(-(2:ℝ))*Menu.sumFee (M i) w
    (∑i,Height.mcount (S:=S) (G:=G) (L:=L) (s:=x) (fun i=>(M i).M)
      A (fun _=>1) ℓ i*R.p.mass (M i).M.crest (M i).M.weight) ≤ Q.goal L x := by
  intro β A
  have h0:0<β:=zero_lt_one.trans_le hβ
  have hp i:0≤A i:=mul_nonneg (Real.rpow_nonneg h0.le _) (Menu.timed _ hw)
  have hm i:0≤R.p.mass (M i).M.crest (M i).M.weight:=
    mul_nonneg (Real.exp_pos _).le (M i).M.profit
  have fee:=(total origin M w hw h).trans hb
  calc
    _ ≤ ∑i,Height.grow G L x*A i*R.p.mass (M i).M.crest (M i).M.weight:=
      Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (one_mark _ A hp hβ i) (hm i)
    _ = (Height.grow G L x*β^(-(2:ℝ)))*
      ∑i,Menu.sumFee (M i) w*R.p.mass (M i).M.crest (M i).M.weight:=by
      rw [Finset.mul_sum]; congr 1;ext i;dsimp [A];ring
    _ ≤ (Height.grow G L x*β^(-(2:ℝ)))*β :=
      mul_le_mul_of_nonneg_left fee (mul_nonneg (Real.rpow_nonneg h0.le _) (Real.rpow_nonneg h0.le _))
    _ = β^(-(5/8:ℝ)):=by
      change β^(3/8:ℝ)*β^(-(2:ℝ))*β=_
      calc
        _ = β^(3/8:ℝ)*β^(-(2:ℝ))*β^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add h0,←Real.rpow_add h0]; norm_num

    _ ≤ Q.goal L x:=Real.rpow_le_rpow_of_exponent_le hβ (by linarith [Q.start])

/-- A charged old physical row cannot also be occupied by an admitted log leaf. -/
theorem same_mcount {ι:Type} (M:ι→Lotus.Leaf R) (D:ℕ→ℝ)
    (hD:∀i,R.activities.E i=0 → D i=1) (ℓ:ℕ) (i:ι) (a:ι→ℝ) :
    Height.mcount (S:=S) (G:=G) (L:=L) (s:=x) M a D ℓ i =
      Height.mcount (S:=S) (G:=G) (L:=L) (s:=x) M a (fun _=>1) ℓ i := by
  cases h:(M i).turn with
  | gasKey u =>
    simp [Height.mcount,Merge.Palette.sign,h,Lotus.Wing.badge,Height.hip,
      Silica.lip]
  | logKey u =>
    have hz:R.activities.E u=0:=by
      simpa only [h,Lotus.Wing.blank] using (M i).blank
    simp [Height.mcount,Merge.Palette.sign,h,Lotus.Wing.badge,Height.hip,
      Silica.lip,Clutch.whip,Raw.wool,hD u hz]

theorem boosted (H:Cash W x μ L Q o C T R) (j n ℓ:ℕ) {h:Stage} {i:ℕ}
    (ticket:Booked j n ℓ P Q E L W μ o h i x)
    (works:Works P L x S T) (stamp:Stamp T) (D:ℕ→ℝ) (cap:Raw.Pumps R D (1*incomingE G L x))
    (blank:∀i,R.activities.E i=0 → D i=1) :
    ∃A b C' d rv s z B e q:ℝ,∃k:ℕ,∃N:Captain H j C' d rv s A b z B e k Chi.canonical,
      ManuscriptQLocalHeightPaidRows.Ready j d B k ∧ HostQ H N.conduit A B k ∧ Bikes Q L μ x E.earn q B j k ∧
      ∀(V ι:Type) [DecidableEq V] [Fintype V] [Fintype ι] (Γ:Census V)
      (M:ι→Menu.Hat Γ R) (origin:V→Site f) (w:V→ℝ) (b':ℝ),
      (∀v,0<w v) → Menu.Offer origin M w R.p.B R.p.supportExponent b' →
      (Fintype.card V:ℝ)*b'≤betaF G x L →
      let a:=fun l=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M l) w
      Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
        (fun z=>Height.beaconN H ℓ z*Height.rocket H D z*
          Height.markU N (fun l=>(M l).M) a z n) E.earn 1 := by
  obtain ⟨hβ,_,_,v,a,_,ha,buyer⟩:=ticket
  obtain ⟨A,b,C',d,rv,s,z,B,e,q,k,N,ready,_,host,bikes,sold⟩:=
    buyer c f S T works stamp R C H D cap
  refine ⟨A,b,C',d,rv,s,z,B,e,q,k,N,ready,host,bikes,?_⟩
  intro V ι _ _ _ Γ M origin w b' hw hOffer hb A₀ atRoot
  have hp l:0≤A₀ l:=mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hβ) _) (Menu.timed _ hw)
  have r:=sold ι inferInstance (fun l=>(M l).M) A₀ hp (by
    simp_rw [same_mcount (S:=S) (L:=L) (x:=x) (fun l=>(M l).M) D blank ℓ]
    exact discounted (Q:=Q) (ℓ:=ℓ) M origin w hw hOffer hβ hb)
  exact budget_loosen (r atRoot) ha

theorem genuine (H:Cash W x μ L Q o C T R) (j n ℓ:ℕ) {h:Stage} {i:ℕ}
    (ticket:Booked j n ℓ P Q E L W μ o h i x)
    (works:Works P L x S T) (stamp:Stamp T) (cap:R.activities.EBound R.p (incomingE G L x)) :
    ∃A b C' d rv s z B e q:ℝ,∃k:ℕ,∃N:Captain H j C' d rv s A b z B e k Chi.canonical,
      ManuscriptQLocalHeightPaidRows.Ready j d B k ∧ HostQ H N.conduit A B k ∧ Bikes Q L μ x E.earn q B j k ∧
      ∀(V ι:Type) [DecidableEq V] [Fintype V] [Fintype ι] (Γ:Census V)
      (M:ι→Menu.Hat Γ R) (origin:V→Site f) (w:V→ℝ) (b':ℝ),
      (∀v,0<w v) → Menu.Offer origin M w R.p.B R.p.supportExponent b' →
      (Fintype.card V:ℝ)*b'≤betaF G x L →
      let a:=fun l=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M l) w
      Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
        (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*
          Height.markU N (fun l=>(M l).M) a z n) E.earn 1 :=
  boosted H j n ℓ ticket works stamp (fun _=>1) (pumps cap) (fun _ _=>rfl)

end Source
end YM.Integration.ManuscriptQLocalMarkedHeight
