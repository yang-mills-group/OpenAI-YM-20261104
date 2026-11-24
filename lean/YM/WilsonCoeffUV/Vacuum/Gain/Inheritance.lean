import YM.WilsonCoeffUV.Vacuum.Gain.UnchangedRanks
/-!
# SAME-component payments on simple real vacuum page.
Wind toll depends strictly on preceding degrees whenever levied.
Readout rank-two calibration charges separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power MultiNext.SignedSource
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{r:ℕ}{α β :Type*}{s t t' σ A B C D E F X:ℝ}{L:Side} {M:ropes Cover (Co L (Hooks G)) (Hooks G)}

def tau₀ (G:Gauge)(r m:ℕ) (B s t σ:ℝ):= preB (Hooks G) r m t (t/2) s σ B
def tauV (G:Gauge)(r:ℕ)(B s t σ:ℝ): ℝ:= match r with
| 0=> tau₀ G 1 3 B s t σ
| j+1=> tau₀ G (j+2) (j+2) B s t σ
def clockB (k:ℕ)(L:Side)(G:Gauge)(r:ℕ)(D t s σ:ℝ):= D^(r+1) * (ceilPoly k (t-t/2)*Real.exp (8*s))*tiePay (Co L (Hooks G)) (r+1) (s-σ)
def mathP (G:Gauge)(L:Side)(r:ℕ)(B s t σ:ℝ) : ℝ:= match r with
| 0=>0
| j+1=>
   let D:=B/(L.val:ℝ)
   ((j+2:ℕ):ℝ)*clockB 1 L G (j+2) (max (D+D+(D+D)) (Fintype.card Axis*D)) t s σ

def mathZ (G:Gauge)(L:Side)(r:ℕ)(B C D s t σ:ℝ): ℝ := let X:= (max (B/(L.val:ℝ)) C)
    ((r+2:ℕ):ℝ)*clockB 0 L G (r+1) (max (X+X) D) t s σ

def postV (G:Gauge)(L:Side)(r:ℕ)(B C D s t σ:ℝ):= mathP G L r B s t σ+mathZ G L r B C D s t σ
lemma clockB_nn (G:Gauge)(L:Side)(k r:ℕ)(h:0≤D)(he:σ<s): 0≤clockB k L G r D t s σ:=by
   unfold clockB; have ht:= ceilPoly_pos k (t-t/2); apply mul_nonneg (by positivity); exact pow_nonneg (boardPay_nn (div_pos (sub_pos.mpr he) (by positivity))) _
lemma mathP_nn (G:Gauge)(L:Side)(r:ℕ)(h:0≤B)(ht:σ<s): 0≤mathP G L r B s t σ:=by
   unfold mathP; cases r; simp only; rfl
   exact mul_nonneg (by positivity) (clockB_nn _ _ _ _ (le_max_of_le_left (by positivity)) ht)
lemma mathZ_nn (G:Gauge)(L:Side)(r:ℕ)(h:0≤B)(ht:σ<s): 0≤mathZ G L r B C D s t σ:=by
   let X:= max (B/(L.val:ℝ)) C; have hh:0 ≤ X := le_max_of_le_left (by positivity)
   exact mul_nonneg (by positivity) (clockB_nn G L 0 (r+1) (le_max_of_le_left (add_nonneg hh hh)) ht)
lemma postV_nn (G:Gauge)(L:Side)(r:ℕ)(h:0≤B)(ht:σ<s):0≤ postV G L r B C D s t σ:= add_nonneg (mathP_nn G L r h ht) (mathZ_nn G L r h ht)
lemma tauV_nn (G:Gauge)(r:ℕ)(h:0≤B)(hp:0<t)(he:σ<s):0≤ tauV G r B s t σ :=by
   have ht:t/2<t:=by linarith
   cases r with
   | zero=> exact preB_nn ht h he ..
   | succ r=> exact preB_nn ht h he ..

def AxisClear {G: Gauge} (P:Gen ℝ (YForest G)) : Prop := Aware (P 2)
lemma slope₁ {r:ℕ}(h:0<s)(he:((r+1:ℕ):ℝ)*s/L.val ≤ t): s/L.val ≤ t:=le_trans (div_le_div_of_nonneg_right (le_mul_of_one_le_left h.le (by norm_cast; omega)) (by positivity)) he

lemma ruby_cut (h:Crank M 3 s B){P:Gen ℝ (YForest G)}(he:Smooth (P (r+2)))(ha:Amber terrain t E (P (r+2)))(hp:Draft (P (r+2)) t X)(g:AxisClear P)(g':stroll (P (r+2))) (hq:0≤σ)(hi:σ<s)(ht:0<t)(hv:((r+2:ℕ):ℝ)*s/L.val≤ t/2):
    Amber terrain σ ((tauV G r B s t σ)*E/L.val+ mathP G L r B s t σ * X) (pump (P (r+2)) (owns L M)) := by
    have ht':t/2<t:=by linarith
    have hs:= lt_of_le_of_lt hq hi; have hv':=slope₁ (r:=r+1) hs hv
    cases r with
    | zero=>
       have hb : ∑ i:Fin 2,chop i=3:=by simp [chop,Fin.sum_univ_two]
       have hu:∀ x,Summable (spinJob (P 2) (owns L M) x):= fun x=> (pump_sum (fun i=>ownS h.polish i) ha hs (hv'.trans ht'.le) x).of_norm
       have HH:= clockOut (r:=1) (P:=P (0+2)) 1 chop (fun i=>by fin_cases i<;>norm_num [chop]) h ha hq hi ht' hv (by rw [hb]; norm_num)
       obtain ⟨hc,H⟩:= HH
       change Amber _ _ (_+ 0*X) _; rw [zero_mul,add_zero]
       rw [←orbitQ M g' g ha ht (show ∀ x,Summable (spinJob (P 2) (paneQ M) x) from hc) hu]; rw [hb] at H; exact H
    | succ j=>
       set r:= j+3
       let p := (0:Fin r)
       let W:= Finset.univ.erase p
       have hz : p∉W:=by simp [W]
       have hb : W.card=j+2:= by simp [W,r]
       let k (i: Fin r):= if i∈ W then (1:ℕ) else 0
       have hw : ∑ i:Fin r,k i=j+2:= by simp [k,hb]
       have H:= (clockOut (r:=j+2) p k (fun i=>by by_cases hh:i∈W <;> simp [*,k]) h ha hq hi ht' hv (by rw [hw]; omega)).2
       have heq : (fun i=>nestTake L M p i (k i))=pareDeck L M p W:=by
          ext1 i; unfold k pareDeck; split; · apply nest_take
          apply nest_base
       set D:= B/(L.val:ℝ); let A:=max (D+D+(D+D)) (Fintype.card Axis*D)
       rw [heq,hw] at H
       have ht'' := (pare_delta (M:=M) p W hz h.polish ha hp he hq hi hv' ht')
       have HG : Amber terrain σ (mathP G L (j+1) B s t σ * X) (pump (P (j+1+2)) (owns L M)- pump (P (j+1+2)) (pareDeck L M p W)):= by
          have hm:= ht''.neg; rw [neg_sub] at hm
          rw [hb] at hm; apply hm.le; exact le_of_eq (by unfold mathP clockB; dsimp only; ring)
       change Amber _ _ _ _
       have he:= H.add HG; rw [add_sub_cancel] at he; exact he

lemma platinum {Q:ropes Cover (Larvae G L) (Hooks G)}{Z: ReaderT L G}(h:Crank M 3 s B)(k:verdant M Q Z)(q:dragCup terrain s C Q)(u:dragCup terrain s D Z){P:Gen ℝ (YForest G)}(he:Smooth (P (r+2)))(ha:Amber terrain t E (P (r+2)))(hp:Draft (P (r+2)) t X)(g:AxisClear P)(g':stroll (P (r+2))) (hq:0≤σ)(hi:σ<s)(ht:0<t)(hv:((r+2:ℕ):ℝ)*s/L.val≤ t/2):
     Amber terrain σ ((tauV G r B s t σ)*E/L.val+ postV G L r B C D s t σ * X) (prism Q (plants L P) (r+2)) := by
  rw [lead_pump]
  let A := mixWind (hh:=h.polish.le (le_max_left (B/L.val) C)) (q.le (le_max_right ..)) k u he ha hp (slope₁ (lt_of_le_of_lt hq hi) hv) hq hi (by linarith : t/2<t)
  have hb:= (ruby_cut h he ha hp g g' hq hi ht hv).add A
  rw [add_sub_cancel] at hb; apply hb.le; exact le_of_eq (by unfold postV mathZ clockB; dsimp only; ring)
end YM.WilsonCoeffUV.Bank
