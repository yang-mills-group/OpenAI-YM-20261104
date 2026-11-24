import YM.Integration.WilsonPhysicalHistoryRetainedProduct
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Weaving

/-! Spend the old signed regular insertion once in the full forest Haar and
Gaussian measurement. All alarms are detected on the same fluctuation. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge}

def insertedCost {ι : Type*} (r e : ι→ℝ) : List ι→ℝ
  | []=>0
  | i::t => e i*(t.map r).prod+r i*insertedCost r e t

private theorem combined {ι : Type*} (v u r e : ι→ℝ)
    (change : ∀ i,|v i-u i|≤e i) (bound : ∀ i,|v i|≤r i ∧ |u i|≤r i)
    (s : List ι) :
    |(s.map v).prod-(s.map u).prod|≤ insertedCost r e s ∧ |(s.map v).prod|≤(s.map r).prod := by
  induction s with
  | nil => simp [insertedCost]
  | cons i s ih =>
    simp only [List.map_cons,List.prod_cons,insertedCost]
    have he : 0≤e i := (abs_nonneg _).trans (change i)
    have hr : 0≤r i := (abs_nonneg _).trans (bound i).1
    constructor
    · calc
        _ = |(v i-u i)*(s.map v).prod+u i*((s.map v).prod-(s.map u).prod)| := by ring_nf
        _ ≤ _ := abs_add_le ..
        _ ≤ _ := by
          rw [abs_mul,abs_mul]
          exact add_le_add (mul_le_mul (change i) ih.2 (abs_nonneg _) he)
            (mul_le_mul (bound i).2 ih.1 (abs_nonneg _) hr)
    · rw [abs_mul]; exact mul_le_mul (bound i).1 ih.2 (abs_nonneg _) hr

private theorem shared_measure {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
    (X : Coat T F) (J : Set (Air f G)) (hm : MeasurableSet J) (a : ℝ) :
    (∫ u : F.Slice G × Air f G,J.indicator (fun _=>a) u.2 ∂((F.order G).prod X.dice))=X.dice.real J*a := by
  letI : IsProbabilityMeasure (F.order G) := by infer_instance
  letI : IsFiniteMeasure (F.order G) := by infer_instance
  letI : SigmaFinite (F.order G) := IsFiniteMeasure.toSigmaFinite _
  letI : SFinite (F.order G) := by infer_instance
  letI : IsProbabilityMeasure X.dice := by infer_instance
  letI : IsFiniteMeasure X.dice := by infer_instance
  letI : SigmaFinite X.dice := IsFiniteMeasure.toSigmaFinite _
  letI : SFinite X.dice := by infer_instance
  let cap (u : F.Slice G × Air f G):=J.indicator (fun _=>a) u.2
  have hc : Integrable cap ((F.order G).prod X.dice) := ((integrable_const a (μ:=X.dice)).indicator hm).comp_snd _
  change (∫ u,cap u ∂((F.order G).prod X.dice))=_
  rw [integral_prod _ hc]
  have cash (y : F.Slice G) : ∫ z,cap (y,z) ∂X.dice=X.dice.real J*a:=integral_indicator_const a hm
  simp_rw [cash]
  rw [integral_const]
  simp only [probReal_univ,one_smul]

theorem molecule_integral (R : Run G) {N n j d : ℕ} (hj : j<N) (A : Comparison R (p:=n) hj d) :
    let P:=R.family.path.rep N n j
    let Q:=approximation R (p:=n) hj d
    let δ:=(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1)
    ∃ b : ℕ→ℝ, (∀ x,SumBudget (fun i=>if (P.activities.reg i).site=x then
      P.p.mass (P.activities.reg i).support (b i) else 0) δ) ∧
      ∀ {c L : Side} {S : StepData c (R.family.side j n)} {T : Tube G S} {F : Forest S.ratio}
        {W μ C x : ℝ} {M : Teller G} {D : ConnectedActivityE6.Target G M} {o : Target.Order G W}
        (H : Cash W x μ L D o C T P) (X : Coat T F),
        X.x=x → X.width=o.K → X.manifest → δ≤1 →
        (∀ (Y : F.Slice G) (l : Finset ℕ) (z : Air (R.family.side j n) G) (i : ℕ),
          |(X.wrapY Y).vertex P D.table W o.a l D.halo z (regularHead S i)|≤1/4) →
        ∀ (l : Finset ℕ) (p : Molecule S),
        let err:=fun v : Head S=>(5/2:ℝ)*regularFee S b v
        ∫ t,|X.body P D.table W o.a l D.halo p t-X.body Q D.table W o.a l D.halo p t|
          ∂((F.order G).prod X.dice) ≤ H.alarms^(blaze p).card*
            insertedCost (fun v=>H.fair v+err v) err p.toList := by
  dsimp only
  obtain ⟨b,pay,rows⟩:=molecule_rows R hj A
  refine ⟨b,pay,?_⟩
  intro c L S T F W μ C x M D o H X ht hy hp small quarter l p
  let f:=R.family.side j n
  let P:=R.family.path.rep N n j
  let Q:=approximation R (p:=n) hj d
  let err (v : Head S):=(5/2:ℝ)*regularFee S b v
  let r (v : Head S):=H.fair v+err v
  let price:=insertedCost r err p.toList
  let J:=X.catastrophe o.ξ P.beta (blaze p)
  let cap (t : F.Slice G × Air f G):=J.indicator (fun _=>price) t.2
  let law:=(F.order G).prod X.dice
  have estimate (y : F.Slice G) (z : Air f G) :
      |X.body P D.table W o.a l D.halo p (y,z)-X.body Q D.table W o.a l D.halo p (y,z)|≤price := by
    let v:=(X.wrapY y).vertex P D.table W o.a l D.halo z
    let u:=(X.wrapY y).vertex Q D.table W o.a l D.halo z
    have bill:=rows (X.wrapY y) D.table W o.a l D.halo z
    have lo (i : Head S) : |v i-u i|≤err i := by
      by_cases proper : ∃ k,i=regularHead S k
      · obtain ⟨k,rfl⟩:=proper
        have paid:=bill.1 k small
        have nn:=nonneg_of_mul_nonneg_right ((abs_nonneg _).trans paid) (by positivity)
        exact paid.trans (mul_le_mul_of_nonneg_right (by linarith only [quarter y l z k]) nn)
      · have un:=bill.2 i (fun k eq=>proper ⟨k,eq⟩)
        change |(X.wrapY y).vertex P _ _ _ _ _ _ i-(X.wrapY y).vertex Q _ _ _ _ _ _ i|≤_
        rw [un,sub_self,abs_zero]
        rcases i with _|_|((k|_)|_)|_
        all_goals first | exact (proper ⟨k,rfl⟩).elim | norm_num [err,regularFee]
    have both (i : Head S) : |v i|≤r i ∧ |u i|≤r i := by
      have first:=H.voice (X.wrapY y) ht hy hp l i z
      have nn:0≤err i:=(abs_nonneg _).trans (lo i)
      refine ⟨first.trans (le_add_of_nonneg_right nn),?_⟩
      calc |u i| = |v i-(v i-u i)| := by ring_nf
           _ ≤ |v i|+|v i-u i| := abs_sub _ _
           _ ≤ r i := add_le_add first (lo i)
    have he:=(combined v u r err lo both p.toList).1
    simpa only [Finset.prod_map_toList,price,Coat.body,Coat.term,v,u] using he
  have outside (y : F.Slice G) (z : Air f G) (away : z∉J) :
      X.body P D.table W o.a l D.halo p (y,z)=0 ∧ X.body Q D.table W o.a l D.halo p (y,z)=0 := by
    have block:=((H.quotes F (X.wrapY y) ht hy hp).2.2.2 (blaze p)).2 l z
    have off : ¬ ∀ i∈blaze p,(X.wrapY y).detect ((X.wrapY y).liftA P.beta z) W o.a P l i≠0 :=
      fun all=>away (block all)
    push Not at off
    obtain ⟨a,ha,zero⟩:=off
    let i : Head S:=.inr (.inr (.inr a))
    have inside : i∈p := Finset.mem_toRight.mp (Finset.mem_toRight.mp (Finset.mem_toRight.mp ha))
    have bz : (X.wrapY y).vertex P D.table W o.a l D.halo z i=0 := zero
    have swap:=(rows (X.wrapY y) D.table W o.a l D.halo z).2 i (by intro t; simp [i,regularHead])
    exact ⟨Finset.prod_eq_zero inside bz,Finset.prod_eq_zero inside (swap.symm.trans bz)⟩
  have hm : MeasurableSet J := Poll.sounded ..
  have hc : Integrable cap law := ((integrable_const price (μ:=X.dice)).indicator hm).comp_snd _
  have paycap (u : F.Slice G × Air f G) :
      |X.body P D.table W o.a l D.halo p u-X.body Q D.table W o.a l D.halo p u|≤cap u := by
    obtain ⟨y,z⟩:=u
    by_cases hz : z∈J
    · simpa only [cap,Set.indicator_of_mem hz] using estimate y z
    obtain ⟨a,b'⟩:=outside y z hz
    simp [cap,Set.indicator_of_notMem hz,a,b']
  have amount : 0≤price := (abs_nonneg _).trans (estimate (1 : F.Slice G) 0)
  apply (integral_mono_of_nonneg (Eventually.of_forall fun _=>abs_nonneg _) hc (Eventually.of_forall paycap)).trans
  refine (shared_measure X J hm price).trans_le ?_
  exact mul_le_mul_of_nonneg_right ((H.quotes F X ht hy hp).2.2.2 (blaze p)).1 amount

end YM.Integration.OriginalMarkedRunAction
