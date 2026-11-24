import YM.WilsonCoeffUV.Emit.ScaleSlots
/-!
# Slot scalar factors in mixed-address LOG and capture model bounds

Restores Π_i w_i. Use to segregate the prescribed polynomial-log coupling
and matrix conversions, since z-only polynomial insufficient for pivot cells
and exp-analytic estimate's gate can't use Λ in place of z.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.ScaleS
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Flooring
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι:Type}{S:Finset ι}{D k K:ι→ℕ}{B i j d a e r h N m b l:ℕ}{G:Gauge}{σ z ρ:ℝ}{E W V U U':Credit}{A: Levels G}{Ñ:ChartRatio G}{R:Realm G (e+1) E}{H:Hol G}{T:ι→SealR G}
section
variable [DecidableEq ι][Fintype ι]
omit [DecidableEq ι] [Fintype ι] in
lemma factoredHealth (w:ι→ℝ){X: Outerm G D}(h:Wellness k X): Wellness k (withinC w X) := by
    refine ⟨fun i=>by unfold withinC compound; rw [h.quiet' i, smul_zero], fun i S=>(h.level' i S).μ _,fun p q S z=>by unfold withinC compound; rw [h.filial _ q S z]⟩
omit [DecidableEq ι] [Fintype ι] in
lemma tariffGrow {w:ι→ℝ}(v:∀ i:ι,0<w i)(Q:ι→SealR G)(X:(s:ι)→ Verse (Q s).F) : onSlots Q (onSlots Q X (fun i=>(w i)⁻¹)) w=X:=by funext i; unfold onSlots; rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (v i)),one_smul]
-- `≤` heights from price; no uniform finset factors hidden
omit [DecidableEq ι] [Fintype ι] in
lemma lookupScale {w:ι→ℝ}(v:∀ i,0<w i)(Q:ι→SealR G)(X:(s:ι)→ Verse (Q s).F)(u:Credit)(p:∀ i,sprouted (Q i) (X i) e (w i*u.buy z))(i): sprouted (Q i) (onSlots Q X (fun i=>(w i)⁻¹) i) e (u.buy z):=by
   intro j q t; rw [onSlots,Pi.smul_apply,map_smul, norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (v i).le)]; exact le_trans (mul_le_mul_of_nonneg_left (p i j q t) (inv_nonneg.mpr (v i).le)) (le_of_eq (inv_mul_cancel_left₀ (v i).ne' _))
omit [Fintype ι] in
lemma openedFactor {P:Outerm G D}(w:ι→ℝ)(p:Wellness k P)(v:m≤N): outset R m N ρ k K (withinC w P)=withinC w (outset R m N ρ k K P):=by
   funext i S; unfold outset; rw [gearsFactor R.hG R.green w p le_rfl v]; change reserveGood _ _ _ _ _ i S=(∏ j∈S,w j) • reserveGood _ _ _ _ _ i S; unfold reserveGood; split; rfl; rw [smul_zero]

abbrev hgate (H:Hol G)(Q:ι→SealR G)(E W V U U':Credit)(e:ℕ)(z:ℝ): ℝ:= galeGate G (fun i=>(Q i).D) (fun i=>(Q i).h) (fun i=>(Q i).h) e ((dictated H Q E W V U e).choose) U' E z
variable (X:(s:ι)→ Verse (T s).F)(w:ι→ℝ) (p:Tribe R H W V T)(U:Credit)
include p in
lemma crossing (q:∀ i,0<w i)(u:R.anchor≤ m)(r:m≤ N)(x:R.y m≤ z)(g:hgate H T E W V U U' e z ≤ρ)(f:∀ i,sprouted (T i) (X i) e (w i*U.buy z))(v:Cloze (fun i=>(T i).D) (fun i=>(T i).h) R U')(Y:ι→ Cover)(S:Finset ι)(hp:1<S.card)(c:m≤ b)(h:b≤N)(δ:cleared R.draws.S m b ρ Y S)(z':i≤e)(l:ℕ):
    let k i:=(T i).h
    Wig Bank.terrain Y (R.mint b (u.trans c)).σ ((∏ i∈S,w i)*Real.exp (-penaltyB U' z ρ (snowP R.draws.S m b))) S ((Gears R.draws R.paid k k N N b (coatA R.draws R.paid N m T X) Y S).2 i l):=by
    let W':=onSlots T X (fun i=>(w i)⁻¹); let C:= (dictated H T E W V U e).choose; let P:=coatA R.draws R.paid N m T W'; let K i:=(T i).h
    have e0: Borealis R (fun i=>(T i).D) K K P m N C z:=(dictated H T E W V U e).choose_spec R p m N W' z u r x (lookupScale q T X U f)
    intro k; have hϕ:= tariffGrow q T X; have hv: Gears R.draws R.paid k k N N b (coatA R.draws R.paid N m T X)=withinC w (Gears R.draws R.paid k k N N b P):=by
        rw [show coatA R.draws R.paid N m T X=withinC w P from hϕ ▸ coatFactor (N:=N) (m:=m) T W' w]; exact gearsFactor R.hG R.green w e0.head le_rfl h
    rw [hv]; let θ:= ∏ j∈S,w j; have hθ:0≤θ:= Finset.prod_nonneg fun i _=> (q i).le
    apply (Wig.μ (coruscate (r:=l) e0 v g c h Y δ hp z') θ).more; rw [Real.norm_of_nonneg hθ]
lemma Finale_factor (F:Garland D)(w:ι→ℝ)(x y:ℝ)(z:CellR){X:Outerm G D} (f: Wellness k X)(K:ι→ℕ): Finale x y z F K (AuthSum (withinC w X))=(∏ i,w i) • Finale x y z F K (AuthSum X):= by
    unfold Finale; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; unfold scrollR AuthSum withinC; rw [levelsFactor (X i) (f.level' i) w]; unfold compound; rw [tuftR,smul_comm]
end
-- full Σ integral. exact before soft
section
variable {T:Fin (a+1)→SealR G} {X:Herit T}{F:Wilt T}
variable (X F) (p:Tribe R H W V T) (w:Fin (a+1)→ℝ)
include p
theorem crop_factor (u:b≤ m)(v:R.anchor≤ m)(mN:m≤ N) (x:∀ i j,i≠j→ ClearDay (F i) (F j) (ρ+14)):
    AutumnDay R.draws R.paid F (onSlots T X w) m b N d=(∏ i,w i) • AutumnDay R.draws R.paid F X m b N d:=by
   unfold AutumnDay; rw [←tuftR]; apply congr_arg _; let A:= R.draws; let B:=R.paid; let θ:=paceT A.S m b; let k:=asp T; let L:=coatA A B N m T X; let P:=outset R m N ρ k k L; let Y:=Gears A B k k N m b P
   let W:=w; let C:= LodeStar A B F (onSlots T X w) m b N θ; let V:= LodeStar A B F X m b N θ; have hx:= cloister p X v mN; have hv: Wellness k P:= reserveSpec _ _ _ _ (Cog _ _ le_rfl L hx R.hG R.green mN)
   have h (o:CellR): locale o C = locale o ((∏ i,w i) • V):=by
        unfold locale; rw [tuftR]; change locale o C = (∏ i,w i) • locale o V
        rw [show locale o C=_ from (close_eq R H T p v mN (onSlots T X w) F o θ u x).symm, coatFactor, openedFactor w hx mN, gearsFactor R.hG R.green w hv mN u, Finale_factor F w θ θ o (Cog _ _ mN P hv R.hG R.green u) k, close_eq R H T p v mN X F o θ u x]
   apply Prod.ext <;> (first | (funext n i j x; exact ContinuousMap.ext fun a=>congr_fun (congr_fun (congr_fun (congr_fun (congr_arg Prod.fst (h a)) n) i) j) x) | (funext i j x; exact ContinuousMap.ext fun a=> congr_fun (congr_fun (congr_fun (congr_arg Prod.snd (h a)) i) j) x))
/-- True-analytic bills with slot factors restored. Angle unaffected.
Keep pledges fixed (quantified) before layout; w can vary with *m* and all
geometry/Heal data. Estimates through announced coefficient orders only. -/
lemma capture_exp (p':∀ i,0<w i)(U:Credit) (u:b≤ m)(v:m≤ N)(h:R.anchor≤ b){Y: Fin (a+1)→ℝ} (t:hgate H T E W V U U' e z ≤ρ)(hp:Cloze (fun i=>(T i).D) (fun i=>(T i).h) R U')(hq: PadRank R b m z)(g:Shipfit R.draws.S T F m b ρ z Y B)(x:∀ i, sprouted (T i) (X i) e (w i*U.buy z))(y:i≤ e)(r d:ℕ):
    let P:= (invoke H T e E W V U U' B).choose; Cork Bank.terrain 0 (Vσ R b h) ((∏ i,w i)*(Real.exp (P.buy z)*(∏ i,Y i))) ((AutumnDay R.draws R.paid F X m b N d).2 i r):=by
    let W':=onSlots T X (fun i=>(w i)⁻¹); have hT:= lookupScale p' T X U x
    have hf: AutumnDay R.draws R.paid F X m b N d=(∏ i,w i) • AutumnDay R.draws R.paid F W' m b N d:=by
        have he:= crop_factor (d:=d) W' F p w u (h.trans u) v g.lens; rwa [show onSlots T W' w=X from tariffGrow p' T X] at he
    let θ:=∏ i,w i; have ht:0≤θ:=Finset.prod_nonneg fun i _=> (p' i).le
    intro P; rw [hf]; apply (Cork.μ ((invoke H T e E W V U U' B).choose_spec R p m b N u v h F Y W' ρ z d hp hq t g hT i y r) θ).cost; rw [abs_of_nonneg ht]
end
end YM.WilsonCoeffUV.Wheel.ScaleS
