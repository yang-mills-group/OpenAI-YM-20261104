import YM.Integration.WilsonVacuumPreResetPeriodEntries

/-! A period packet contains a genuine finite rotation and site label and
one countable atom label. Its latter label is unchanged by every signed
lattice motion, including for the corrected quadratic payload. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPeriodIndex
open Function Finset Lattice Wilson RG Marker WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat RG01Estimate IterationFour.Vacuum
open Comparison.Density Comparison.Density.Render AnalyticBridge VerifiedReset WilsonStartup
open Extra.Iteration Push.AbsoluteSums
open WilsonVacuumPreResetPeriodEntries
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

private def frame (n:Side)(a:PrismA G):Frame G n:=
  match a with
  | ⟨_,0,_,P⟩=>Frame.makeRose P n 1 Frame.full
  | ⟨_,_+1,_,P⟩=>rack n P 1 Frame.full

private theorem issued (B:BudgetPoint)(σ C:ℝ)(a:PrismA G):
    (FundedCorrectedPeriod.piece n B σ C a).packet.labels=(frame n a).shelf ∘ numbering (Cycle n) ∧
    (FundedCorrectedPeriod.piece n B σ C a).packet.action=(frame n a).table ∘ numbering (Cycle n):=by
  obtain ⟨d,r,rank,P⟩:=a
  cases r <;> exact ⟨rfl,rfl⟩

def depth (n:Side):SeriesA G → ℕ → ℕ
  | [],i=>i
  | _::l,i=>(Payload.coding i).elim (depth n l) (fun j=>(numbering (Cycle n) j).2)

private def pool (n:Side)(t:ℕ):Finset ℕ:=
  ((univ:Finset (Seat n)) ×ˢ range t).map (numbering (Cycle n)).symm.toEmbedding

def indices (n:Side):(SeriesA G) → ℕ → Finset ℕ
  | [],t=>range t
  | _::l,t=>((indices n l t).disjSum (pool n t)).map Payload.coding.symm.toEmbedding

theorem before (Z:SeriesA G)(t i:ℕ):i∈indices n Z t ↔ depth n Z i<t:=by
  induction Z generalizing i with
  | nil=>exact mem_range
  | cons a l ih=>
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    cases j with
    | inl j=>simpa [indices,depth] using ih j
    | inr j=>simp [indices,depth,pool]

structure Moving (A:ℕ → RegularAddress n)(f:ℕ → Config G n → ℝ)(v:ℕ → ℕ)(s:Signed)(b:Site n) where
  mirror:Caddy.Mirrors A s b f
  tier (i:ℕ):f i≠0 → v (mirror.walks i)=v i

private theorem packet (B:BudgetPoint)(σ C:ℝ)(a:PrismA G)(s:Signed)(b:Site n):
    let P:=(FundedCorrectedPeriod.piece n B σ C a).packet
    Nonempty (Moving P.labels P.action (fun j=>(numbering (Cycle n) j).2) s b):=by
  dsimp only
  obtain ⟨h,g⟩:=issued (n:=n) B σ C a
  rw [h,g]
  let m:=Frame.move (frame n a) (Pane.pale n G) ((Pane.whey n G B).moves s b).some
  refine ⟨⟨⟨m.ep,m.reg_site,m.reg_support,fun i=>funext (m.valuesE i)⟩,?_⟩⟩
  intro i _
  let Y:=numbering (Cycle n)
  let T:=Equiv.prodCongr (Seat.move s b) (Equiv.refl ℕ)
  have h:Y (m.ep i)=T (Y i):=Y.apply_symm_apply _
  calc
    _=(T (Y i)).2:=congrArg Prod.snd h
    _=(Y i).2:=rfl

private theorem join (A:Activities G n)(P:Payload G n)(d z:ℕ → ℕ)(c:ℝ)(s:Signed)(b:Site n)
    (L:Moving A.reg A.E d s b)(M:Moving P.labels P.action z s b):
    let H:=P.attach c A
    Nonempty (Moving H.reg H.E (fun i=>(Payload.coding i).elim d z) s b):=by
  let e:=(Payload.coding.trans (Equiv.sumCongr L.mirror.walks M.mirror.walks)).trans Payload.coding.symm
  have he (j):e (Payload.coding.symm j)=Payload.coding.symm (j.map L.mirror.walks M.mirror.walks):=by
    simp [e]
  refine ⟨⟨⟨e,?_,?_,?_⟩,?_⟩⟩
  · rintro i
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    rw [he]
    cases j with
    | inl j=>simpa [Payload.attach] using L.mirror.hooks j
    | inr j=>simpa [Payload.attach] using M.mirror.hooks j
  · rintro i
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    rw [he]
    cases j with
    | inl j=>simpa [Payload.attach] using L.mirror.hues j
    | inr j=>simpa [Payload.attach] using M.mirror.hues j
  · rintro i
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    rw [he]
    cases j with
    | inl j=>simpa [Payload.attach] using L.mirror.posts j
    | inr j=>
      simp only [Payload.attach,Function.comp_apply,Equiv.apply_symm_apply,Sum.map_inr,Sum.elim_inr,Pi.smul_apply,M.mirror.posts]
      rfl
  · intro i hf
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    change (Payload.coding (e (Payload.coding.symm j))).elim d z=(Payload.coding (Payload.coding.symm j)).elim d z
    rw [he]
    cases j with
    | inl j=>
      simpa [Payload.attach] using L.tier j (by simpa [Payload.attach] using hf)
    | inr j=>
      simp only [Equiv.apply_symm_apply,Sum.map_inr,Sum.elim_inr]
      exact M.tier j (fun hz=>hf (by simp [Payload.attach,hz]))

theorem original (B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(k:ℕ → ℕ → ℝ)(s:Signed)(b:Site n):
    let A:=entries n B σ C Z k
    Nonempty (Moving A.reg A.E (depth n Z) s b):=by
  induction Z with
  | nil=>
    let q:=((Pane.whey n G B).moves s b).some
    exact ⟨⟨⟨q.ep,q.reg_site,q.reg_support,fun i=>funext (q.valuesE i)⟩,fun i h=>(h rfl).elim⟩⟩
  | cons a l ih=>
    let P:=(FundedCorrectedPeriod.piece n B σ C a).packet
    exact join (entries n B σ C l k) P (depth n l) _ (k a.grade (a.rise+2)) s b ih.some (packet B σ C a s b).some

end YM.Integration.WilsonVacuumPreResetPeriodIndex
