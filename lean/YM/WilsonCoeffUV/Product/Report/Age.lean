import YM.WilsonCoeffUV.Product.Report.WaveMark
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Aging in stitched financial estimate
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b b' u m M N a:ℕ}{H:Hol G} {x δ Z y:ℝ} {E W V' W':Credit}{R:Realm G (e+1) E}
variable {Q:Fin (a+1)→ SealR G}{T:Wilt Q}{F:Fin (a+1)→ℝ}
abbrev snowP (S: Schedule)(m i:ℕ):= S.scale i-S.scale m
open Real
lemma winterH (S:Schedule)(p:m ≤ i): (↑(i-m):ℝ) ≤ snowP S m i:=by
    induction i,p using Nat.le_induction with
    | base=> simp [snowP]
    | succ i h ih=>
       have ht:1 ≤ Bank.PathCost.arc S i:= le_trans (show (1:ℝ) ≤ Real.log 3 from by rw [Real.le_log_iff_exp_le (by norm_num)]; exact exp_one_lt_three.le) (PathCost.arch_pos S i)
       have hx:i+1-m=i-m+1:=by omega
       rw [hx]; unfold snowP at *; unfold Bank.PathCost.arc at ht; push_cast; linarith
-- Motif not used.
def ageFund (E:Credit): Credit:= let T:= Credit.leanC.prodC (pur 2); ((T.plus T).plus (E.usingC T)).plus (Credit.unit)
lemma gardenP (p:R.anchor ≤ m)(v:m≤ i)(g:R.y m≤ Z):
    let k:= snowP R.draws.S m i; let A:= ageFund E; let L:=A.buy (Z+k);
    Z≤ L∧ Compar R.draws.S R.y m (i+1) ≤ L ∧ PadRank R m i L :=by
    intro k A L; let S:=R.draws.S; have hZ:1≤Z:= (R.depth m p).trans g; let T:= Credit.leanC.prodC (pur 2); let y:= Z+k; let b:= T.buy y; have hp:0≤ k:= sub_nonneg.mpr (scales _ v); have hx:1≤ y:= hZ.trans (le_add_of_nonneg_right hp)
    have hb : 2*y≤ b:=by unfold b T; rw [Credit.products, Credit.lean_cost]; rw [mul_comm (2:ℝ)]; exact mul_le_mul_of_nonneg_left (pure_goal ..) (zero_le_one.trans hx)
    have hv:b≥ y:=by linarith
    have he: Compar S R.y m i ≤ b:=by unfold Compar; have he:= winterH S v; change R.y m + k+ (↑(i-m):ℝ) ≤ b; unfold y at hb; linarith
    have hBuy: Z≤ b:=le_trans (le_add_of_nonneg_right hp) hv; have hP := PadRank.frugal R p v
    let C:= E.usingC T; have hh: 2*b+C.buy y+1≤L:=by
         unfold L A ageFund; apply le_trans _ (Credit.fuel ((T.plus T).plus C) Credit.unit hx); rw [Credit.unit_cost]; exact add_le_add_left ((show 2*b+C.buy y=b+b+C.buy y by ring) ▸ ((add_le_add_left (Credit.fuel T T hx) (C.buy y)).trans (Credit.fuel _ C hx))) _
    have hL:b≤ L:= by linarith only [hh,hx.trans hv,C.purchase hx]
    let P:ℝ:= (S.block i).val; have hu: R.y i≤ b:= (hP.year i v le_rfl).trans he
    have hf : S.scale (i+1)-S.scale i ≤ C.buy y:=by
        have hm : P ≤ E.buy b:= le_trans (R.taxes i (p.trans v)).height (E.elder (R.depth _ (p.trans v)) hu); have ht:0<P:=by unfold P; positivity
        unfold C; rw [Credit.stock_up]; change _≤ E.buy b; rw [Schedule.scale_succ]; linarith only [Real.log_le_sub_one_of_pos ht, hm, show Real.log (↑(S.block i).val)= Real.log P from rfl]
    refine ⟨hBuy.trans hL,?_,⟨fun i q t=>(le_trans ((hP.year i q t).trans he) hL),hP.lengthS.trans (he.trans hL)⟩⟩
    unfold Compar at *; rw [show i+1-m=i-m+1 by omega]; push_cast; unfold S at *; linarith
lemma prices_t (T:Credit)(h:1≤Z)(v:0≤x) : T.buy (Z+x) ≤ T.behind.buy Z * Real.exp (x/8):=
    (T.raised Credit.liftA (Z+x) Credit.lift_good (by linarith)).trans ((T.swell Credit.lift_good h (by linarith) (le_refl (Z+x)) v).trans (mul_le_mul_of_nonneg_right (T.donation _ _ Z h) (by positivity)))
lemma pace_escort (h:R.anchor≤ m)(p:m≤ i): Escort R m i (paceT R.draws.S m):=by refine ⟨h,p,fun i _ _=>(pace_pos ..).le,fun i v _=>pace_le _ v,fun i _ _=>?_⟩; unfold thinLevel; exact le_of_eq (Eq.symm ((eq_div_iff (by positivity)).mpr (pace_step ..)))
-- smooth overlap seam throughout at fixed demand including δ≥ not necessarily equality
abbrev Blizzard (A:Levels G)(Ñ:ChartRatio G)(F:Wilt Q)(U:Herit Q)(m i N:ℕ)(y:ℝ)(o:CellR): Era G ℝ:= cruises A Ñ N (capP Q) i m (Ash A Ñ F U m i N y o)
lemma Fringed.fees {V W: Era G ℝ}{d:ℝ}(q:Fringed k e u y A δ V W)(v:A ≤ B)(t:A*δ≤ B*d)(h:0 ≤ d):Fringed k e u y B d V W:=⟨q.inkV,q.pen,h,fun i j v'=>by let Q:=q.heapS i j v'; exact ⟨Q.wax.more v,Q.wane.more v,Q.toll.more t⟩⟩
theorem PalmDay (H:Hol G)(Q:Fin (a+1)→ SealR G)(E W V W' L:Credit)(e u:ℕ): ∃ C:Credit,∀ (R:Realm G (e+1) E), HorizonP H R W V Q→ SpringD R (capP Q) u (capP Q+2) W' → Dormitory R (capP Q) u L → ∀ m i b N M (F:Wilt Q)(X Y: Herit Q)(A B:Fin (a+1)→ℝ) (Z y δ)(o:CellR), R.anchor ≤ m→ m≤ i → i<b → b≤N → b≤ M → R.y m≤ Z → Bough Q F y Z B → R.tempC m b≤ δ → Sitting Q A e δ X Y →
    let T:= ∏ i,B i*A i; Fringed (capP Q) e u 1 (C.buy Z*paceT R.draws.S m i*T) δ (Blizzard R.draws R.paid F X m i N y o) (Blizzard R.draws R.paid F Y m i M y o):=by
    let d:= ageFund E; let k:=capP Q; let D:=doubling E
    obtain ⟨C,hC⟩:=waveMark H Q E W V W' e u 2; obtain ⟨S,hS⟩:=waveSeen G k e u E L; let F:= S.prodC C; let A:= (F.prodC D).usingC d; let U:= (F.usingC d).behind; let X:= A.behind; let C':=X.plus U
    refine ⟨C',fun R H' p v m i b N M F' P Q' B A' Z y δ o hm hi ht hn hM hz hy hp l=>?_⟩; intro x; let g:= snowP R.draws.S m i; let Y:= d.buy (Z+g); obtain ⟨hv,hq,h⟩:= gardenP hm hi hz; have HH:1≤ Y:=hy.pos.trans hv
    let θ:= D.buy Y*Real.exp (g/4); have hg:0≤g:= sub_nonneg.mpr (scales _ hi); have hxg:1≤ θ:= one_le_mul_of_one_le_of_one_le (Credit.purchase _ HH) (Real.one_le_exp (by positivity)); have hδ:0≤δ:= (trail_pos ..).le.trans hp
    have he : δWarm R i b≤ θ*δ:= by
      have hh: R.tempC i b = Real.exp (g/4)*R.tempC m b:=by unfold tempC g trailC snowP; rw [←Real.exp_add]; congr 1; ring
      unfold δWarm θ; rw [hh,mul_assoc]; exact mul_le_mul (Credit.elder _ (R.depth _ (hm.trans hi)) (h.year _ hi le_rfl)) (mul_le_mul_of_nonneg_left hp (by positivity)) (by have hh:0≤R.tempC m b:= (trail_pos ..).le; positivity) (zero_le_one.trans (Credit.purchase _ HH))
    let V':= paceT R.draws.S m; let η:= V' i; let W':= C.buy Y*η^2*x
    have ha:= hC R H' p m i b N M F' P Q' B A' Y y (θ*δ) o hm hi ht hn hM hq (boughRise hy hv) he (l.gainP (le_mul_of_one_le_left hδ hxg))
    have ht': R.tempC i b≤ θ*δ:= (le_mul_of_one_le_left (trail_pos ..).le (show 1≤R.cash D i from Credit.purchase _ (R.depth _ (hm.trans hi)))).trans he
    have hZ:=hS R v m i V' b N M W' (θ*δ) Y (pace_escort hm hi) h ht.le hn hM ht' _ _ ha
    rw [show V' m=1 from pace_self ..] at hZ; refine hZ.fees ?_ ?_ hδ
    all_goals
       have hη:η=Real.exp (-g):= pace_rep ..
       have hx:0≤x:=Finset.prod_nonneg (fun i _=> mul_nonneg (hy.lanes i).1 (l.stock i))
       have hG:= hy.pos
    · rw [show S.buy Y * W'= (F.usingC d).buy (Z+g)*η^2*x by unfold W' Y F; rw [Credit.stock_up, Credit.products]; ring]; change _≤ Credit.buy _ _ *η*x; apply mul_le_mul_of_nonneg_right _ hx; rw [hη]; refine (mul_le_mul_of_nonneg_right (prices_t _ hG hg) (by positivity)).trans ?_; rw [mul_assoc,← Real.exp_nat_mul,←Real.exp_add]; exact mul_le_mul (Credit.thickened _ hG) (Real.exp_le_exp.mpr (by norm_num; linarith)) (by positivity) (zero_le_one.trans (C'.purchase hG))
    · rw [show S.buy Y*W'*(θ*δ)=(A.buy (Z+g)*Real.exp (g/4)*η^2)*x*δ by unfold W' θ Y A F; simp only [Credit.stock_up,Credit.products]; ring]; apply mul_le_mul_of_nonneg_right _ hδ; apply mul_le_mul_of_nonneg_right _ hx; change A.buy _ * _ * η^2≤ _*η; rw [hη]; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (prices_t _ hG hg) (by positivity)) (by positivity)).trans ?_; rw [mul_assoc (Credit.buy ..),mul_assoc (Credit.buy ..),← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]; exact mul_le_mul (Credit.thickens _ hG) (Real.exp_le_exp.mpr (by norm_num; linarith)) (by positivity) (zero_le_one.trans (C'.purchase hG))
end YM.WilsonCoeffUV.Mer
