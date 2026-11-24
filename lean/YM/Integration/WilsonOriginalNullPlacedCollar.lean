import YM.Integration.WilsonOriginalNullPlacedReserve
import YM.Integration.WilsonOriginalNullCorridor

/-! A canonical physical source can be pushed through a finite
sequence of actual children in engineering units. It retains all
inherited measured and exceptional terms in one Wilson coefficient. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedCollar
open Function Filter Lattice RG Wilson Extra.Histories Source Labels Bid
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullCorridor
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "S₀" => (C₀).localSection d
local notation "F₀" => (C₀).labels.level d

def cost (η:ℝ) (b t:ℕ):=Real.exp (((d:ℝ)+η)*((C₀).S.scale t-(C₀).S.scale b))

theorem stage {η:ℝ} (η0:0<η) : ∀ᶠ i:ℕ in atTop,
    (factor C₀ i)^d*R.y (R.alloy.B.a.clock.J (i+1))+Doors.rate (R.alloy.B.a.S.block i)
      ≤ (factor C₀ i)^((d:ℝ)+η) := by
  filter_upwards [factor_large C₀ η η0] with i priced
  let L:=factor C₀ i
  let σ:=stock C₀ (i+1)
  let c:=R.y (R.alloy.B.a.clock.J (i+1))
  have L1:1 ≤ L:=(factor_positive C₀ i).le
  have β:1 ≤ σ:=(GermGraph.stage C₀ (i+1)).columns_ge
  have r:Doors.rate (R.alloy.B.a.S.block i) ≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos L1 (by norm_num)
  have one:1 ≤ L^d:=one_le_pow₀ L1
  have lhs:L^d*c ≤ L^d*σ:=mul_le_mul_of_nonneg_left (WilsonOriginalNullPlacedReserve.currency R i).2 (zero_le_one.trans one)
  have other:1 ≤ L^d*σ:=one_le_mul_of_one_le_of_one_le one β
  calc
    _ ≤ L^d*σ+L^d*σ := add_le_add lhs (r.trans other)
    _ ≤ L^d*(4*σ) := by nlinarith only [zero_le_one.trans other]
    _ ≤ L^d*L^η := mul_le_mul_of_nonneg_left priced.2 (zero_le_one.trans one)
    _ = _ := by rw [Real.rpow_add (zero_lt_one.trans_le L1),Real.rpow_natCast]

theorem join (η:ℝ) (b i:ℕ) :
    cost R d η b i*(factor C₀ i)^((d:ℝ)+η)=cost R d η b (i+1) := by
  unfold cost;rw [Real.rpow_def_of_pos (zero_lt_one.trans (factor_positive C₀ i)),←Real.exp_add,Schedule.scale_succ];congr 1;ring

theorem edges (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {η:ℝ} (η0:0<η) :
    ∀ᶠ i:ℕ in atTop, ∀ N p, i<N → ∀ (y:Site ((C₀).side (i+1) p))
      (q:Coefficient F₀ ((C₀).side (i+1) p)) (M:ℝ),
      let upper:=(C₀).path.rep N p (i+1)
      let lower:=(C₀).path.rep N p i
      let o:=((C₀).path.levels.clock.op i p).ratio.parent y
      let bill:=(factor C₀ i)^((d:ℝ)+η)*M
      q.Format y (C₀).params upper → q.remBound y upper (safety C₀ (i+1)) M → (F₀).coeffSize q.x ≤ M →
      ∃ z:Coefficient F₀ ((C₀).side i p), z.Format o (C₀).params lower ∧ z.remBound o lower (safety C₀ i) bill ∧
        (F₀).coeffSize z.x ≤ bill ∧ transition (C:=C₀) d N p i (q.density y S₀ upper)=z.density o S₀ lower := by
  filter_upwards [stage R d η0,WilsonOriginalNullPlacedRough.original R d simple shop] with i wage hear
  intro N p live y q M upper lower o bill fit paid x
  obtain ⟨z,zf,zp,zh,push⟩:=hear N p live y q M fit paid
  have M0:0 ≤ M:=(Work.G08.size_nonneg (F₀) q.x).trans x
  have cf:0 ≤ (factor C₀ i)^d*R.y (R.alloy.B.a.clock.J (i+1)) :=
    mul_nonneg (pow_nonneg (zero_lt_one.trans (factor_positive C₀ i)).le _) (WilsonOriginalNullPlacedReserve.currency R i).1
  have roof:WilsonOriginalNullPlacedRough.fare R d i ((F₀).coeffSize q.x) M ≤ bill:=calc
    _ ≤ (factor C₀ i)^d*R.y (R.alloy.B.a.clock.J (i+1))*M+Doors.rate (R.alloy.B.a.S.block i)*M :=
      add_le_add (mul_le_mul_of_nonneg_left x cf) le_rfl
    _ = ((factor C₀ i)^d*R.y (R.alloy.B.a.clock.J (i+1))+Doors.rate (R.alloy.B.a.S.block i))*M := (add_mul _ _ _).symm
    _ ≤ bill := mul_le_mul_of_nonneg_right wage M0
  exact ⟨z,zf,rem_mono zp roof,zh.trans roof,push⟩

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {η:ℝ} (η0:0<η) :
    ∃ onset:ℕ, ∀ b≥onset, ∀ N p, ∀ (y:∀ i,Site ((C₀).side i p)) (n:ℕ),
      b+n≤N → (∀ j<n, ((C₀).path.levels.clock.op (b+j) p).ratio.parent (y (b+j+1))=y (b+j)) →
      ∀ (q:Coefficient F₀ ((C₀).side (b+n) p)) (M:ℝ),
      let upper:=(C₀).path.rep N p (b+n)
      let lower:=(C₀).path.rep N p b
      let bill:=cost R d η b (b+n)*M
      q.Format (y (b+n)) (C₀).params upper → q.remBound (y (b+n)) upper (safety C₀ (b+n)) M →
      (F₀).coeffSize q.x ≤ M →
      ∃ z:Coefficient F₀ ((C₀).side b p), z.Format (y b) (C₀).params lower ∧ z.remBound (y b) lower (safety C₀ b) bill ∧
        (F₀).coeffSize z.x ≤ bill ∧ flow C₀ d N p b n (q.density (y (b+n)) S₀ upper)=z.density (y b) S₀ lower := by
  obtain ⟨u,gate⟩:=eventually_atTop.mp (edges R d simple shop η0)
  refine ⟨u,?_⟩;intro b hb N p y n
  induction n with
  | zero =>
    intro live route q M upper lower bill fit paid head
    have unit:bill=M:=by dsimp only [bill,cost,Nat.add_zero];rw [sub_self,mul_zero,Real.exp_zero,one_mul]
    exact ⟨q,fit,unit.symm ▸ paid,unit.symm ▸ head,rfl⟩
  | succ j ih =>
    intro live route q M upper lower bill fit paid head
    let l:=(factor C₀ (b+j))^((d:ℝ)+η)*M
    obtain ⟨h,hf,hp,hh,push⟩:=gate (b+j) (by omega) N p (by omega) (y (b+j+1)) q M fit paid head
    rw [route j (Nat.lt_succ_self _)] at hf hp push
    obtain ⟨z,zf,zp,zh,actual⟩:=ih (by omega) (fun k hk=>route k (by omega)) h l hf hp hh
    have fitbill:cost R d η b (b+j)*l=bill:=by
      change cost R d η b (b+j)*((factor C₀ (b+j))^((d:ℝ)+η)*M)=cost R d η b (b+j+1)*M
      rw [←mul_assoc,join]
    refine ⟨z,zf,fitbill ▸ zp,fitbill ▸ zh,?_⟩
    change flow C₀ d N p b j (transition (C:=C₀) d N p (b+j) (q.density _ S₀ upper))=_
    exact (congrArg (flow C₀ d N p b j) push).trans actual

end YM.Integration.WilsonOriginalNullPlacedCollar
