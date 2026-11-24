import YM.WilsonCoeffUV.Emit.PhysicalClock
import YM.WilsonCoeffUV.Reclosure.Technical
/-!
# Afford keeping the low REAL path prescription in a model

The repeated-component proof uses aggregated kernels, NOT a change of
representative at every step in a stronger norm. Independent persistent
budgets are polynomial in y (including publication in invariant analytic
packets). For the real comparison the needed *extra* path packets through
any order can render against the E prescription's potentially MUCH larger precise
low path prescriptions. That's a **separate** one-level expense: the bill
includes the same allowance `Calendar.loopCap` as that side does, not
asserted to be `poly(zz)` (measure `profile.paths` separately). It thus
can be priced as a geometry expense (`Expense.lean` proves in monitoring
units, not actual integrals) even without constructing the physical
`R` to meet a polynomial-in-z cap on the loop PRICE; kernel widths still
pre. Do not use this expense in an iterated formal UV cap. No clipping or
real support change, no containment result for `Rep`, `supBounds` or K.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Physical
open RG Function Filter Lattice Source Power Laurent Wilson Blue FreeResolvent Work.F08
open Precision Next.Foundations Input Supply WilsonCoeffLease
open Embroider Soil Cosmos Bank Bank.Mosaic Polestar Ticket
open Mer Patrol Wheel Wheel.Flooring Wheel.Cadenza
open PowerSeries Wheel.Mark
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{W:Prepaid0 G}{P:Funds0 G}{K:KernelChoices}{C:Family G}
variable {s: Sheet G}{l: Rolls s}{A :Levels G}{e m N:ℕ}{X:ℕ→ℕ}{R:Protection l}{V:Delays R}{w:Bar V}{f:Wait w}
variable {σ a B u:ℝ}

lemma paths_lower {P:PathData G}{c:Clip}(h:P.Bounds c σ a B)(hp:0<u)(hz:u≤σ): P.Bounds c u a B:=by
  have hh {e:ℕ}(g:ℕ→Atom G e)(x:ℝ)(w:SumBudget (fun i=>(g i).budget σ) x): SumBudget (fun i=>(g i).budget u) x:=by
    apply budget_minor w (fun i=>?_)
    · intro i; unfold Atom.budget; gcongr; exact Finset.sum_nonneg fun _ _=>abs_nonneg _
    · unfold Atom.budget; exact mul_nonneg (Finset.sum_nonneg fun _ _=> abs_nonneg _) (Real.exp_pos _).le
  refine { h with width:=hp, two:=hh _ _ h.two,three:=hh _ _ h.three,four:=hh _ _ h.four, rows:=fun i=>?_ }
  apply budget_minor (h.rows i) (fun _=>by positivity)
  intro j; gcongr

/-- Computable only in classical mathematics. Chosen BEFORE block. -/
def untilWidth (G:Gauge)(q:ℕ)(b :ℝ)(p:0<b): ℝ:= (circled G q p).choose
lemma until_positive (G:Gauge)(q:ℕ)(b :ℝ)(p:0<b): 0<untilWidth G q b p:= (circled G q p).choose_spec.choose_spec.1
def postReserve (G:Gauge)(q:ℕ)(b:ℝ)(p:0<b): ℝ:= (circled G q p).choose_spec.choose
lemma post_res_nn (G:Gauge)(q:ℕ)(b:ℝ)(p:0<b): 0≤postReserve G q b p:= (circled G q p).choose_spec.choose_spec.2.2.1

/-- `Epic` is the incoming comparison width. Choose Γ according to
 blockers. The outgoing `postGuard` includes reciprocal of granted width
 after `circled` post-lift, and its cost is bounded by a Credit polynomial
 in `T.y` on the bill. Use at any one horizon separately; `against_Kin`
 includes also cost of keeping the loop cap. -/
def Epic (T:Realm G (e+2) Credit.leanC) (_q:m≥T.anchor) (p:5≤ T.draws.clock.J (m+1)) := min (crestM T.draws m p) (T.draws.params m).width
lemma epic_good (T:Realm G (e+2) Credit.leanC) (q:m≥T.anchor) (p:5≤ T.draws.clock.J (m+1)) : 0<Epic T q p:= lt_min (spatter G _ _ _ _ p).1 (T.draws.params m).width_pos

def postGuard (G:Gauge)(q:ℕ)(t:Stage)(b:ℝ)(p:0<b):ℝ:=
    postReserve G q b p+(untilWidth G q b p)⁻¹ + (t.clip.direct+t.paths+t.paths*t.paths)

def Minted (T: Realm G (e+2) Credit.leanC) (V: Credit): Prop:= ∀ m (a:m≥T.anchor),∃ i:5≤T.draws.clock.J (m+1), (T.mint m a).σ=crestM T.draws m i ∧ postGuard G e (T.draws.params m) _ (epic_good T a i)≤ V.buy (T.y m)

theorem against_Kin (G:Gauge)(q:ℕ)(Z:Credit): ∃ W:Credit,∀ (T:Realm G (q+2) Credit.leanC), Minted T Z →
    ∀ (H:Horizon T.draws)(P:Kin H T.paid) {t:Sheet G}{l:Rolls t}(V:PostCost l), P.Planned V →
    ∀ m (a:m≥T.anchor),∃ p:5≤ T.draws.clock.J (m+1),
      let σ:= untilWidth G q (Epic T a p) (epic_good T a p)
      0<σ ∧ σ⁻¹≤ Z.buy (T.y m) ∧∀ N, m≤N →
        let R:=P.path N m
        let C:= (T.draws.params m).clip
        let A:=actionW T.draws T.paid N m
        ∃ X:SeriesA G,(∀ i∈X,3 ≤ i.grade) ∧ fromBefore X (3+q) ∧ X.length ≤ meterPre (3+q) ∧ Draw X σ (W.buy (T.y m)+Z.buy (T.y m)* T.draws.clock.loopCap m) ∧
          ∀ i, i<3+q → (breast R C+sandLift X) i=A i ∧ ∀ n:Side,∀ r,(front R C n+sands X n) i (r+1)= lagoon (A i (r+1)) n:=by
  obtain ⟨U,hU⟩:= full_vacuum G (q+2) Credit.leanC
  refine ⟨Z.prodC (Z.plus U),fun T H M P _ _ V hp m a=>?_⟩
  obtain ⟨b,hb,h⟩:= H m a; let K:= T.draws.params m
  let y:=T.y m; let A:=Z.buy y; let z:=Epic T a b; have hz:0<z:=epic_good T a b
  let c:=untilWidth G q z hz; have hc:0<c:=until_positive ..; let C':=postReserve G q z hz; have hC:0≤ C':= post_res_nn ..
  let D:= K.clip.direct+K.paths+K.paths*K.paths; have hD: 0≤D:=by unfold D; have hv:= K.clip.quadratic_pos; have hs:=K.paths_pos; positivity
  have ht:C'+c⁻¹+D≤A:=h; have hu:0≤c⁻¹:= (inv_pos.mpr hc).le
  refine ⟨b,hc,by change c⁻¹≤A; linarith,fun N hk=>?_⟩; dsimp only
  have hf: (P.path N m).Bounds K.clip z K.paths (T.draws.clock.loopCap m):= paths_lower (hp.cap N m hk) hz (min_le_right ..)
  have hy:= T.depth _ a
  have hK:0≤U.buy y:= zero_le_one.trans (Credit.purchase U hy)
  have hh (i:ℕ)(hi:i<3+q) : Desc (actionW T.draws T.paid N m) i z (U.buy y) := by
     apply these T.hG T.green hk; intro r
     apply ((hU i (by omega) r T m a m N N le_rfl hk hk).pose).mono
     rw [hb]; exact min_le_left ..
  obtain ⟨X,h1,h2,h3,h4,H⟩:= (circled G q hz).choose_spec.choose_spec.2.2.2 (P.path N m) K.clip (actionW T.draws T.paid N m) K.paths (T.draws.clock.loopCap m) (U.buy y) hK hf (alpha_stable T.hG T.green hp hk).1 (fun i p=> ⟨hh i p,fun j s x=> (catchment T.draws T.paid T.hG T.green hk).signs s 0 i j x⟩)
  let Λ:=T.draws.clock.loopCap m
  have ht:0≤Λ:= (PhysicalNext.Repeat.Pane.coverBill ..).1
  have hv:C'≤A:=by linarith
  refine ⟨X,h1,h2,h3,h4.light le_rfl ?_,H⟩
  rw [Credit.products]; change C'*(D+Λ+U.buy y)≤ A*(Z.plus U).buy y+A*Λ
  calc
    _≤ A*(D+Λ+U.buy y):= mul_le_mul_of_nonneg_right hv (by linarith)
    _ = A*(D+U.buy y)+A*Λ:=by ring
    _≤ _ := by apply add_le_add_left; apply mul_le_mul_of_nonneg_left _ (by linarith); exact (add_le_add_left (show D≤A by linarith) _).trans (Credit.fuel _ _ hy)

/-- This input may be made bigger regardless of L. Snapshot Stage selected
pre-L. postGuard does not require L. -/
lemma stock_c (s:Sheet G)(X:ℕ→ℕ)(j:ℕ): ∀ᶠ c:ℝ in atTop,∀ (A:Levels G),A.clock.kernel=s.kernel→A.clock.stage=s.profile→ ∀ m, A.clock.J (m+1)=j → ∀ (hj:5 ≤ A.clock.J (m+1)) (e:ℕ), e ≤ X j → postGuard G e (A.params m) _ (lt_min (show 0<crestM A m hj from (spatter G _ _ _ _ hj).1) (A.params m).width_pos)≤ c:=by
  have he (i:ℕ) : ∀ᶠ c:ℝ in atTop,∀ (t : ℕ), t  ≤  X j → ∀ (g:4 ≤ i)(p:5 ≤ j), postGuard G t (s.profile i) _ (lt_min (spatter G s.kernel i j g p).1 (s.profile i).width_pos) ≤ c:=by
    filter_upwards [ (eventually_all_finset (Finset.range (X j+1))).mpr fun t _=> (eventually_all.mpr fun g:4 ≤  i=>(eventually_all.mpr fun p:5 ≤ j=>eventually_ge_atTop (postGuard G t (s.profile i) _ (lt_min (spatter G s.kernel i j g p).1 (s.profile i).width_pos))))] with c h
    exact fun i t=> h i (Finset.mem_range.mpr (Nat.lt_succ_of_le t))
  filter_upwards [(eventually_all_finset (Finset.range (j+1))).mpr fun i _=> he i] with c ht
  intro A q w m y a e t
  subst j; let i:=A.clock.J m; have hz: A.params m=s.profile i:= congr_fun w _
  have he:crestM A m a=splash G s.kernel i (A.clock.J (m+1)) (A.clock.adm m) a := by unfold crestM; simp_rw [q]; rfl
  generalize_proofs h
  revert h; rw [he,hz]; intro; exact ht i (Finset.mem_range.mpr (Nat.lt_succ_of_le (A.fits.mono m.le_succ))) e t (A.clock.adm _) a

def RunLease (G:Gauge) (X:ℕ→ℕ)(P:Funds0 G): Funds0 G := fun s R t =>
     { P s R t with betaEntry:= (fun j=>Real.exp (Real.exp (eventually_atTop.mp (stock_c s X j)).choose)) ⊔ (P s R t).betaEntry }

-- yields cross-royalty. Consumer with same C.
variable {u0:ℕ→Gear G→ℝ} (L: Leased C K (moreL G X W) (later G X u0 (RunLease G X P)))
include L
lemma renewed : Push.PriceCompiler.DelayLe (P L.page L.phases L.cert) L.delays:= by
  obtain ⟨z,i,h,p⟩:=(paid_clock L).1
  exact ⟨(sup_le_iff.mp z).2,i,h,p⟩

lemma tallies {T:Realm G (e+2) Credit.leanC}(h:T.draws=C.path.levels)(hx:T.y=zz T.draws) (v:∀ i (p:T.anchor ≤ i),∃ j:5 ≤ T.draws.clock.J (i+1), (T.mint i p).σ=crestM _ _ j ∧ e≤ X (T.draws.clock.J (i+1))) : Minted T Credit.leanC :=by
  intro m b; rw [Credit.lean_cost,hx]; obtain ⟨j,hj,z⟩:=v m b
  refine ⟨j,hj,?_⟩
  let A:=T.draws; let B:= A.clock.J (m+1)
  have he : L.delays.betaEntry B ≤ A.clock.hatBeta m:=by unfold B A; rw [h]; exact L.proof.pays _
  have hp : (fun j:ℕ=>Real.exp (Real.exp (eventually_atTop.mp (stock_c L.page X j)).choose))≤ L.delays.betaEntry:= (sup_le_iff.mp (paid_clock L).1.beta).1
  have hf:= redeemBill (show (fun j:ℕ=>Real.exp (Real.exp (eventually_atTop.mp (stock_c L.page X j)).choose)) B ≤ Real.exp (Real.exp (zz A m-1)) from ((hp B).trans he).trans_eq (scaledBills A m))
  have hK : T.draws.clock.kernel=L.page.kernel:=by rw [h]; exact L.proof.kernel
  have hv : T.draws.clock.stage=L.page.profile:=by rw [h]; exact L.proof.stage
  exact (eventually_atTop.mp (stock_c L.page X B)).choose_spec _ hf A hK hv m rfl j e z

theorem base_lease (hp:G.Simple)(v:Tendsto X atTop atTop)(e:ℕ) : ∀ᶠ m:ℕ in atTop,∃ T:Realm G (e+2) Credit.leanC, T.draws=C.path.levels∧ T.anchor=m∧ T.paid=chart G∧ T.y=zz T.draws∧ Minted T Credit.leanC:=by
  let A:= C.path.levels; let i k:= A.clock.J (k+1); have ht:Tendsto i atTop atTop:= A.fits.deep.comp (tendsto_add_atTop_nat 1)
  have hx:= (v.comp ht).eventually_ge_atTop e
  obtain ⟨p',hq⟩:= eventually_atTop.mp hx
  let J:=fun _:Fin 1=> 1; let S:=fun _:Fin 1=> 0
  filter_upwards [stars L hp v 1 S J (fun _=>by simp [S,J]) 1 (e+1) 0,eventually_ge_atTop p'] with n h hn
  obtain ⟨T,h,u,p,z,q,w,s,r⟩:=h; have hu:T.y=zz T.draws:=p.trans (congr_arg zz h.symm)
  refine ⟨T,h,z,u,hu,tallies L h hu fun k t=>?_⟩
  have ht:= z ▸ t; obtain ⟨j,hj,x⟩:= r k ht t
  let b:= T.draws.clock.J (k+1); have hp:b=A.clock.J (k+1):=by unfold b; rw [h]
  have hf:5≤ b:= hp.symm ▸ j
  exact ⟨hf,hj.trans (by unfold crestM; congr 1 <;> rw [h]), by change e ≤ X b; rw [hp]; exact hq k (hn.trans ht)⟩
end YM.WilsonCoeffUV.Physical
