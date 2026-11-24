import YM.LocalLTE.Drift.Aura
/-!
## Slip transactions for the cost estimator

Cylinders may be accessed by these *same* ports.
Personal program used on incoming
models, body validity for another actual magnitude cannot substitute for the receipts
on that model. Norm uses all links in site sets. Energy bills overbook
some binomial/readout prices; K includes none of the PDF normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Drift
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{k d:ℕ}{F:Labels.Frame G d} (D:SectionData F) (A:Hol G)
local notation "O" => H.rep N p m
local notation "P" => H.rep N p (m+1)
local notation "V₀"=> H.S.side (m+1) p
local notation "V"=> H.S.side m p
local notation "κ" => Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "κ'" => Real.sqrt (H.levels.clock.forcedAllowance (m+1))
-- model book.RQ acceptable for ALL desks incl output capacities not enough for a paid model.As long after.L scheduled sender.
open Extra.Histories.InputColumn
open Drift
local notation "R'"=> H.rep N p (m+1)
local notation "Gp"=> Config G (H.S.side (m+1) p)
-- Catalog from Bank. import uses integer horizon K. Real rows only incl witness layouts.
variable {K S:ℕ}{k:ℕ→ℕ}{F₁:ℕ→ Coefficient F (H.S.side (m+1) p)}
set_option quotPrecheck false
variable {l γ:ℝ} {s s' e: ℕ→ℝ}
variable (U:Gateway F A (H.rep N p (m+1)) (H.S.side m p)) (T:Drift.Etching D A (H.rep N p (m+1)) (H.S.side m p) k K S l)
variable (w:ℕ){A0:ℝ}(t:ℕ→ℕ→ℝ) -- t.Error costs per predictor query
variable (C:TariffX)(hx:Works D A (H.rep N p (m+1)) (H.rep N p m) w U T (Real.sqrt (H.levels.clock.forcedAllowance m)) C)(hp:F.coeffSize (Vinca.unitP F H p m|>.x) ≤ C.token.issue)

variable {Y:F.Coeff→ ℕ→ Coefficient F (H.S.side (m+1) p)}
variable (W:Voice F H p (m+1))(X:Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)(P':Employ H N p A m W X) (i:F.Index)
local notation "vV"=> H.rep N p (m+1)
local notation "y"=> W.index.symm (Size.axis F i)
local notation "u₀"=> (H.levels.params (m+1)).columns
local notation "a"=> W.plays y
local notation "c"=> W.charge y
local notation "T0" j=> Vinca.parcelP H N p A m W X U P' j
variable (Y':Paper (H:=H) (m:=m) (N:=N) (p:=p) D A (Y (W.index.symm (Size.axis F i))) K k S l s s')

-- cumulative layers ports. Patron delta budget deliberately normalized to λ.
-- assign taper ceremonies. Motion.V.St.
structure Book (D:SectionData F)(A:Hol G)(R:Rep G (H.S.side m p))(W:Voice F H p m)(Y:F.Coeff→ ℕ→ Coefficient F (H.S.side m p))(K:ℕ)(k:ℕ→ℕ)(w:ℕ)(l κz:ℝ)(s s' e:ℕ→ℝ) : Prop where
    annual v j (h:j ≤ K): Exhibition D l w (k j) A R (W.plays v) (Y v j) κz (s j * F.coeffSize (W.index v)) (e j*F.coeffSize (W.index v))
    lifts v j (_h:j < K): Patrons D l w (k (j+1)) R.p (Vinca.decrement (Y v (j+1)) (Y v j)) (s' j * F.coeffSize (W.index v))
open Motion
variable (hk:Book D A (H.rep N p (m+1)) W Y K k S l (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) s s' e) (hy:Heard D H N p A (m+1) W)
-- no `C.token` Theta rank-change for each Apostle. actual painter on Ribbon uses real voices.
variable {A0:ℝ}

local notation "S0"=> ((H).rep N p m)
include hk in
lemma axisV j (ht: j≤K): Exhibition D l S (k j) A (H.rep N p (m+1)) (W.plays (W.index.symm (Size.axis F i))) (Y (W.index.symm (Size.axis F i)) j) κ' (s j) (e j):=by
   have hv:= hk.annual (W.index.symm (Size.axis F i)) j ht; rw [LinearEquiv.apply_symm_apply,Size.size_axis, mul_one,mul_one] at hv; exact hv
lemma inlet (hk:Book D A (H.rep N p (m+1)) W Y K k S l (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) s s' e): Nonempty (∀ i:F.Index, Paper (H:=H) (m:=m) (p:=p) (N:=N) D A (Y (W.index.symm (Size.axis F i))) K k S l s s'):=by
   have hp i j (he:j<K):= hk.lifts (W.index.symm (Size.axis F i)) j he; simp_rw [LinearEquiv.apply_symm_apply,Size.size_axis,mul_one] at hp; exact ⟨fun i=>Classical.choice (Drift.scrolls D A _ (Drift.axisV _ A _ i hk) (hp i))⟩ -- order
variable (Υ : ∀ i:F.Index,Paper (H:=H) (m:=m) (p:=p) (N:=N) D A (Y (W.index.symm (Size.axis F i))) K k S l s s') (V':Voice F H p m)(hL:V'.plays=Vinca.marksP H N p A m W X U P')
noncomputable def proceedX (f:F.Coeff)(j:ℕ): Coefficient F (H.S.side m p) := if h:j≤K then pencil (code (Tally F)) (fun r:Tally F=> audition (P'.turns r.1) (Drift.colors D A U T W X P' r.2 (Υ r.2) j h)) ((chips F).comp W.index.toLinearMap) f else Extra.Histories.primary (0:Site (H.S.side m p)) 0
local notation "q0"=> proceedX D A U T W X P' Υ
local notation "ν"=> (fun i:ℕ=> (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))*(e i+e i))
local notation "vZ"=> (H.levels.params (m+1)).columns
local notation "f" => (F)
local notation "R"=> rotationP F (S0).p.order (S0).p.power
local notation "g"=> orbitCost F
local notation "t1"=> (fun i=>R*(C.peak vZ s s' e i)*g)
local notation "t2"=> (fun i=>R*(C.delta vZ s s' e ν i)*g)
local notation "tv"=> (fun i=>R*(C.slip vZ s s' e (i+1)+C.slip vZ s s' e i)*g)
variable (hK:∀ j, j<K→ k j ≤ k (j+1))(hD:D.Sound A){κV:ℝ}(hr:ConnectedActivityE6.Reliable G l κV)
include hp hx hk hy hL hK hD hr
lemma harvest (v:F.Coeff) : let B:= F.coeffSize (W.index v); ((∀ j:ℕ,j ≤ K→ Exhibition D l w (k j) A (H.rep N p m) (V'.plays v) (q0 v j) κ (t1 j* B) (t2 j * B))∧ ∀ j:ℕ,j<K→ Patrons D l w (k (j+1)) ((H.rep N p m).p) (Vinca.decrement (q0 v (j+1)) (q0 v j)) (tv j*B)) :=by
   intro B; let t:= (Tally F); let Yk (q:Tally F)(j:ℕ)(hj:j≤K):=Drift.colors D A U T W X P' q.2 (Υ q.2) j hj
   have hs(i) := Drift.rainbowU D A U T w C hx hp W X P' i (Υ _) (Drift.axisV D _ W i hk) hy -- order
   let St:= vZ; let η i:= C.peak St s s' e i; let τ:=C.delta St s s' e ν; let Zv i:= C.slip St s s' e (i+1) + C.slip St s s' e i
   let u q:= W.index q
   let Z(q:Tally F) := audition (P'.turns q.1) (Vinca.parcelP H N p A m W X U P' q.2); let α (q:t):ℂ:=chips F (W.index v) q
   let A'(r:Tally F)(j:ℕ)(hj:j≤K):= audition (P'.turns r.1) (Yk r j hj)
   let Xv(q:Tally F):= Extra.Histories.stretch (α q) (Z q); let W'(j:ℕ)(hj:j≤K)(q:Tally F):= Extra.Histories.stretch (α q) (A' q j hj)
   have hn: 2 ≤ (H.S.side m p).val:= (show 2 ≤ 4 from by omega).trans (Next.Foundations.actual_side_ge ..)
   have hh(j:ℕ)(hj:j≤K)(q:Tally F): Exhibition D l w (k j) A (H.rep N p m) (Xv q) (W' j hj q) κ (‖α q‖*(R*η j)) (‖α q‖*(R*τ j)):=River.Exhibition.buckets _ (River.pitch q.1 (P'.turns q.1) ((hs q.2).1 j hj) hD hr hn)
   have hX : V'.plays v= Extra.Histories.merge (code _) Xv:=by rw [hL]; rfl
   have hQ j (hq:j ≤ K): q0 v j=Extra.Histories.merge (code _) (W' j hq):=dif_pos hq
   have hκ:0 < Real.sqrt (H.levels.clock.forcedAllowance m):= Real.sqrt_pos.mpr (Extra.Histories.forcedPos ..)
   have hΨ (v0:ℝ)(hv:0 ≤ R*v0): ∑' i,(‖α i‖*(R*v0)) ≤ R*v0*g*B:=by
       rw [tsum_fintype,← Finset.sum_mul]; apply (mul_le_mul_of_nonneg_right (MergeProof.rip F _) hv).trans; unfold B; apply le_of_eq; ring
   have h₀:0 ≤ R:=zero_le_one.trans (River.rotation_one ..)
   constructor
   · intro j hj; rw [hX,hQ j hj]; exact (River.auctions _ _ _ (hh j hj) Summable.of_finite Summable.of_finite hκ).pledge (hΨ _ (mul_nonneg h₀ (hs (0:F.Index)|>.1 j hj|>.stock.cost))) (hΨ _ (mul_nonneg h₀ ((hs (0:F.Index)|>.1 j hj).fee.first)))
   intro j hj; rw [hQ _ hj,hQ _ hj.le]
   have hp q : Patrons D l w (k (j+1)) ((H.rep N p m).p) (decrement (W' (j+1) hj q) (W' j hj.le q)) (‖α q‖*(R*Zv j)):=by
       unfold W'; have hx(Q₀ Q: Coefficient F (H.S.side m p)): Vinca.decrement (Extra.Histories.stretch (α q) Q₀) (Extra.Histories.stretch (α q) Q)= Extra.Histories.stretch (α q) (decrement Q₀ Q):=by simp [Extra.Histories.stretch,decrement, smul_sub]
       rw [hx]; apply River.dollar
       unfold A'; rw [River.glide]; apply River.takes _ _ ((hs q.2).2 j hj (hK _ hj)) _ hD hr hκ hn; exact River.offFormat ((hs q.2).1 (j+1) hj|>.format) ((hs q.2).1 j hj.le|>.format) ((hs q.2).1 j hj.le|>.stock.forced) (((hs q.2).1 _ hj|>.layout.symm).trans ((hs q.2).1 j hj.le|>.layout))
   let Uv:= (W' j hj.le); have hZ (q):= ((hh j hj.le q).large le_rfl le_rfl (hK j hj) le_rfl)
   have ht:= River.remounted (code _) (W' _ hj) (W' j hj.le) hκ (fun i=> (hh (j+1) hj i).format) (fun i=> (hh j hj.le i).format) (fun i=> ((hh (j+1) hj i).layout).symm.trans ((hh j hj.le i).layout)) (fun i=> (hh (j+1) hj i).stock) (fun i=> (hZ i).stock) hp Summable.of_finite Summable.of_finite Summable.of_finite
   exact ht.priced (hΨ (Zv j) (mul_nonneg h₀ ((hs (0:F.Index)).2 j hj (hK _ hj)|>.cost)))
end YM.LocalLTE.Drift
