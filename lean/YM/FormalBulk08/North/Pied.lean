import YM.FormalBulk08.North.Hub

/-! Extend cover output to independent infinite step. Priceable books via explicit limits. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.North
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I J:Type}{G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{E:ℕ}{W:Lab G K I}
abbrev porch (x:Leaf W.scrolls) := stageFoot W.scrolls x 1
def limY (x:Leaf W.scrolls): Row (BoardL G (W.pat x) (W.wood x.a x.b)) (BoardL G (W.pat x) (W.wood x.a x.b)) := dye (unitRow _) (Mean W x.a x.b) 0 (unitRow _)
def limG (x:Leaf W.scrolls): Row (BoardL G (W.pat x) (W.wood x.a x.b)) (BoardL G (W.pat x) (W.wood x.a x.b)):= dye (Cov W x.a x.b) 0 0 0
-- book at cut
abbrev Postal (G: Gauge)(W:Lab G K I)(x:Leaf W.scrolls)(y:J→ℕ)(z: J):= destination (W.V x.a) (y z) x.b
-- skip `G` unused rename
variable (x:Leaf W.scrolls)(hp:Use W ρ E)
abbrev seqN (i:ℕ):= i+ (x.b+1)
abbrev coinR (i:ℕ):=fare_n (porch x) (seqN x i)
lemma coinP (i:ℕ): 0≤coinR x i:= (ratioR_pos ..).le
lemma coinD : Ends (coinR x) 0:= (tendsto_add_atTop_iff_nat _).2 (fare_fin (porch x))
def ticket (j:ℕ): Row (BoardL G (W.pat x) (W.wood x.a x.b)) (BoardL G (W.pat x) (W.wood x.a x.b)):= zealand K (destination (W.V x.a) (seqN x j) x.b) (W.wood x.a x.b) G
def booket (j:ℕ): Row (BoardL G (W.pat x) (W.wood x.a x.b)) (BoardL G (W.pat x) (W.wood x.a x.b)):= rayshot (destination (W.V x.a) (seqN x j) x.b) (W.wood x.a x.b) (W.toEmpire.bill x.a x.b)
include hp
lemma meet_land : Maori (V:=fun _=>BoardL G (W.pat x) (W.wood x.a x.b)) staticT (fun _=> W.windowD x) (coinR x) (ticket x) (fun _=>limY x) := by
    obtain ⟨u,v⟩:= ongoing hp x; let C:=W.callL x ρ E; have hx:C≥0:= (W.turn_whose hp x).plus.le; let R:=max 1 C; have hR:0≤R:=zero_le_one.trans (le_max_left ..);let M:=W.windowD x
    have hh: (limY x).strip M R:= fileStrip (strip_mono Work.F08.strip_unit le_rfl (le_max_left ..)) (strip_mono u.value le_rfl (le_max_right ..)) (stillborn hR) (strip_mono Work.F08.strip_unit le_rfl (le_max_left ..))
    refine ⟨⟨_, soft_coin _ R,fun _=> hR,fun i=>?_⟩,⟨_,soft_coin _ R,fun _=>hR,fun _=>hh⟩,_, soft_coin _ C,fun _=>hx,fun i=>?_⟩
    · exact zealandPay K (destination (W.V x.a) (seqN x i) x.b) _ (u.stays _ (by unfold seqN;omega))
    have he:= u.price (seqN x i) (by unfold seqN;omega); have h0:0≤C*coinR x i:=mul_nonneg hx (coinP x i)
    change (minusRows (dye (unitRow _) (MeanP W x.a x.b (seqN x i)) (0:Row (Loc G 1) _) (unitRow _)) (limY x)).strip _ _;unfold limY;erw [gaps]; exact fileStrip (stillborn h0) he (stillborn h0) (stillborn h0)
lemma graspG: Gilt staticT (fun _=> fame (BoardL G (W.pat x) (W.wood x.a x.b))) (fun _=> W.windowD x) (coinR x) (fun i=>lands (booket x i)) (fun _=> lands (limG x)):= by
    let C:=W.callL x ρ E; obtain ⟨u,v⟩:=ongoing hp x; have he:C≥0:= (W.turn_whose hp x).plus.le;let H:ℝ:=(Fintype.card (BoardL G (W.pat x) (W.wood x.a x.b)))*C; have hx i:= ray_cover (destination (W.V x.a) (seqN x i) x.b) (W.wood x.a x.b) (W.toEmpire.bill x.a x.b) (hp.zero x).le he (v.stays _ (by unfold seqN;omega))
    have hp (i j): Ends (fun k=> lands (booket x k) i j) (lands (limG x) i j):= by
        rcases i with ⟨w,a|b⟩ <;> rcases j with ⟨z,c|d⟩
        · exact (tendsto_add_atTop_iff_nat (x.b+1)).mpr (v.moves a c (z-w))
        all_goals exact tendsto_const_nhds
    have hv: (limG x).strip (W.windowD x) C:= fileStrip v.value (stillborn he) (stillborn he) (stillborn he)
    refine ⟨⟨fun k i j=>(hx k).2 i j,_,soft_coin _ H,fun k=>(hx k).1⟩,⟨fun _ i j=> tendsto_nhds_unique (hp i j) ((hp j i).congr' (.of_forall fun k=>(hx k).2 _ _)),_,soft_coin _ H, fun _=>gratia hv he⟩,_,soft_coin _ H,fun _=>mul_nonneg (Nat.cast_nonneg _) he, fun i=>?_⟩
    obtain ht:= voltage (0:Row _ (Loc G 1)) 0 0 (v.price (seqN x i) (by unfold seqN;omega)) (show 0≤C*coinR x i from mul_nonneg he (coinP x i))
    unfold H; rw [mul_assoc];exact ht
end YM.FormalBulk08.North
