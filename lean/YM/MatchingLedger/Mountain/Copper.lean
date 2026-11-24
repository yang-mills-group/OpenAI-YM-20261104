import YM.MatchingLedger.Mountain.Crossing

/-!
 # Principal path book *including true loop carry*. Rooted split at Site n and signed channel;
 pair labels retain **both** paths with full LENGTHS. Supports determined by written terms; lift
 price multiplied into θ. Full summability (even for order 5) after those width payments.
 -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.MatchingLedger.Mountain.Miner
open Set Function Filter Precision RG MeasureTheory Lattice Wilson Metric Push.Uniform Exterior
open Work.F02 Extension.UV.LoopRate Extension.UV.StationaryData
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge} {n:Side} {p:Clip} {W:PathData G} {σ C Λ:ℝ}
local notation "E"=> fieldDir G n 1
variable (q : Signed)(a:Site n) {μ:ℝ} (hp:0<μ)(ht:2*μ≤σ) (hh:μ≤1) (k:ℕ) (hW:W.Bounds p σ C Λ)

-- record families, not directly averaging all labels
def iron (p:Clip) (v : PlaqAxes) (x:E) : ℝ := p.direct * G.price (faceValue (fortune q x) (a,v))
def ironFee (G:Gauge) (k:ℕ):= |priceCost G (travelCost G k 4 (amount G k))|
include hW hp hh
omit hp in
lemma iron_income : revenue 1 k μ (fun _ : PlaqAxes=>4) (iron (G:=G) q a p) (Real.exp 4 * ironFee G k * Fintype.card PlaqAxes):=by
   let P:=ironFee G k; have hv:0≤P:= abs_nonneg _
   refine ⟨fun _=>P,fun _=> hv,⟨fun _=>mul_nonneg (Real.exp_pos _).le hv,(hasSum_fintype _).summable, by rw [tsum_fintype, Finset.sum_const,Finset.card_univ,nsmul_eq_mul,(by simp: ((↑(4:ℕ)):ℝ)=(4:ℝ))]; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone (by linarith only [hh]: μ*4 ≤ 4)) hv) (Nat.cast_nonneg _)) (le_of_eq (mul_comm ..))⟩,fun i u hx=> ?_⟩
   let d:=p.direct; let H: Walk := square i.val.1 i.val.2
   have he:= travel_jets (U:=fun (x:E)=>fortune q x) (w:=H) (allows_signed q k u hx) a (show H.length≤4 from le_rfl); let w:=fun x:E=>G.price (faceValue (fortune q x) (a,i)); have hx: Allows k (fun x=> d • w x) u (|d| *priceCost G (travelCost G k 4 (amount G k))):= (Allows.price (f:=fun x:E=> travel (fortune q x) a H) he).smul d
   apply hx.mono; have hd : 0<d:= p.quadratic_pos
   rw [abs_of_pos hd]; exact (mul_le_mul (Push.PriceCompiler.Canonical.direct_le_one hW.metric) (le_abs_self _) (Allows.price (f:=fun x:E=> travel (fortune q x) a H) he).nonneg zero_le_one).trans_eq (one_mul _)

abbrev Metal := PlaqAxes ⊕ (PlaqAxes × (ℕ×ℕ)) ⊕ ℕ ⊕ ℕ

-- width at actual underlying directed slots
def travels (W:PathData G): Metal→ ℕ:= Sum.elim (fun _=>4) (Sum.elim (fun i=> fare₁ i.1 W i.2) (Sum.elim (fun i=> (W.cubic i).length) (fun i=>(W.quartic i).length)))
def slope (p:Clip)(W:PathData G): Metal→ E→ ℝ:= Sum.elim (iron q a p) (Sum.elim (fun i=> bunion W q a i.1 i.2) (Sum.elim (fun i x=> (W.cubic i).unmasked (fortune q x) a) (fun i x=> (W.quartic i).unmasked (fortune q x) a)))

def slid (W: PathData G)(i:ℕ)(x:E):= (W.loop i).unmasked (fortune q x) a
def turnL (W: PathData G)(i:ℕ) := (W.loop i).length

def compass₀ (G:Gauge)(k:ℕ)(C μ:ℝ):= Real.exp 4 * ironFee G k* Fintype.card PlaqAxes+((Fintype.card PlaqAxes:ℝ)*garnet G k C μ+(C*value G k 3 μ+C*value G k 4 μ))
def compass₁ (G:Gauge)(k:ℕ)(Λ μ:ℝ):= Λ*value G k 2 μ
include ht in
lemma asks : revenue 1 k μ (travels W) (slope q a p W) (compass₀ G k C μ) ∧ revenue 1 k μ (turnL W) (slid q a W) (compass₁ G k Λ μ):=by
   let P:=amount G k
   have hx:= located q a hp ht k hW
   have hy:= revenue.staple hx
   rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hy
   exact ⟨(iron_income q a hh k hW).pair (hy.pair ((atom_price q a hp ht k W.cubic C hW.three).pair (atom_price q a hp ht k W.quartic C hW.four))), atom_price q a hp ht k W.loop Λ hW.two⟩
omit hp hW hh

-- price identity per channel.Hull position support carried.
include hW hp ht k in
lemma collapses {X:E}(hx:X∈ball 0 1) :
    (∑' i,slope q a p W i X)= (∑ i : PlaqAxes,(p.direct * G.price (faceValue (fortune q X) (a,i)) + ‖W.ell (fortune q X) (a,i)‖^2/2)) + ((∑' i,(W.cubic i).unmasked (fortune q X) a) + ∑' i,(W.quartic i).unmasked (fortune q X) a) :=by
   let f:=fun i:Metal=> slope q a p W i X; let g:=(f ∘ Sum.inr); let h:=(g ∘ Sum.inr); let w:= (g ∘ Sum.inl)
   have hh:Summable (h ∘ Sum.inl):= (atom_price q a hp ht k _ _ hW.three).values hp.le hx; have hv:Summable (h ∘ Sum.inr):= (atom_price q a hp ht k _ _ hW.four).values hp.le hx
   have hz:= Summable.sum h hh hv
   have hW': Summable w:=(revenue.staple (located q a hp ht k hW)).values hp.le hx
   rw [Summable.tsum_sum (f:=f) (hasSum_fintype _).summable (Summable.sum g hW' hz), tsum_fintype]; change _+(∑' i,g i)=_
   rw [Summable.tsum_sum (f:=g) hW' hz]; change _+((∑' i,w i)+∑' i,h i)=_
   rw [Summable.tsum_sum (f:=h) hh hv, hW'.tsum_prod, tsum_fintype, Finset.sum_add_distrib]
   have h i : ∑' j,w (i,j)= ‖W.ell (fortune q X) (a,i)‖^2/2:= revenue_bunion q a hp ht k hW i hx
   simp_rw [h]
   exact (add_assoc ..).symm

include hp hW ht k in
lemma recorded {X:E}(hx:X∈ball 0 1): AT n p W X= Patch.average (fun q:Signed=>∑ x:Site n,∑' i, slope q x p W i X):=by
   simp_rw [collapses _ _ hp ht k hW hx]; unfold AT; dsimp only [Function.comp_apply]; simp_rw [mainTerm, quadratic, Fintype.sum_prod_type, uncut, fortune,Finset.sum_add_distrib,add_assoc]
lemma loaded (X:E): L n W X= Patch.average (fun q:Signed=>∑ x:Site n, ∑' i, slid q x W i X):= rfl
end YM.MatchingLedger.Mountain.Miner
