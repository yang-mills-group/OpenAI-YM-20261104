import YM.FormalBulk08.Trellis.Band
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Trellis
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{W: Lab G K X}{ρ:ChartRatio G}{E e r d D R:ℕ}{o:Loc G 1}{F:Frame G d}{H:Hol G}{T:SectionData F}
variable (q:Quota F H W o D E R)(u:Use W ρ E)(h: LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤ R)(x:Leaf W.scrolls)
include q u h a hs ht hb hr
lemma orig (i j:Letter F)(he:e≤ E): Ends (fun k=> coeff e (bornM (T:=T) (ρ:=ρ) (W:=W) a q.horizon x.a (seqN x k) x.b i j)) (coeff e (tableau F a ρ T q.horizon x i j)) := quietP (coinD x) (coinP x) (terraceF q u h a hs ht hb hr x i j e he)
lemma lures : Found (slots F) (Pose.weight F) (tableau F a ρ T q.horizon x) (fun i=> heightK ((W.V x.a).S.block x.b) d (Pose.weight F i)) ∧ ∀ e≤ E,∀ i j, slots F j+e < slots F i→ coeff e (tableau F a ρ T q.horizon x i j)=0:= by
   have hp n:=(mat_begins a h q hs ht hb x.a x.b (seqN x n) x.zone (by unfold seqN;omega)).1; let U:=tableau F a ρ T q.horizon x
   have hv e (he:e≤E) (i j:Letter F) (H:slots F j+e < slots F i): coeff e (U i j)=0:= tendsto_nhds_unique (orig q u h a hs ht hb hr x i j he) (tendsto_const_nhds.congr' (.of_forall fun n=> ((hp n).bound i j e H).symm))
   exact ⟨⟨fun i j h=>hv 0 (Nat.zero_le _) i j h,(hp 0).paid,fun i j H hx=> tendsto_nhds_unique (orig q u h a hs ht hb hr x i j (Nat.zero_le _)) (tendsto_const_nhds.congr' (.of_forall fun n=> ((hp n).diagonal i j H hx).symm))⟩,hv⟩
lemma staticBack (i j:Letter F): Priced staticT (coinR x) (fun k=> (bornM (ρ:=ρ) (T:=T) (W:=W) a q.horizon x.a (seqN x k) x.b)⁻¹ i j) (fun _=> (tableau F a ρ T q.horizon x)⁻¹ i j) E:= prize_back (u:=slots F) (w:=Pose.weight F) (b:=fun _ i=>heightK _ _ _) (fun i=>down (mat_begins a h q hs ht hb x.a x.b (seqN x i) x.zone (by unfold seqN;omega)).1) (fun _=> (lures q u h a hs ht hb hr x).1) (fun i=>soft_coin _ _) (terraceF q u h a hs ht hb hr x) i j
lemma runwayBack (i j: Letter F): Priced (purseP W) (spinR targetPower) (fun x=> (bornM (ρ:=ρ) (T:=T) (W:=W) a q.horizon x.a x.top x.b)⁻¹ i j) (fun x=> (bornM (ρ:=ρ) (T:=T) (W:=W) a q.horizon x.a x.summit x.b)⁻¹ i j) E := by
    let v(X:transferPoint W)(i:Letter F):= heightK ((W.V X.a).S.block X.b) d (Pose.weight F i)
    refine prize_back (u:=slots F) (w:=Pose.weight F) (b:=v) (fun i=> down (mat_begins a h q hs ht hb i.a i.b i.top i.zone i.wing).1) (fun i=> down (mat_begins a h q hs ht hb i.a i.b i.summit i.zone (i.wing.trans_le i.extra)).1) (fun i=>?_ ) (Elm.staccato q u h hs ht hb a hr) i j
    refine (soft_coin _ 1).below (fun j=>?_); have hp:1≤v j i:= crown_weight _ i; rw [abs_of_nonneg (by positivity), abs_one]; exact inv_le_one_of_one_le₀ hp
-- invoice exact variation uniform before geometry; latter if needed for pivots.
lemma opening (he:e≤ E) (i j: Letter F) : Faint (purseP W) (spinR targetPower) (fun x=> coeff e (bornM (ρ:=ρ) (T:=T) (W:=W) a q.horizon x.a x.top x.b i j)-coeff e (tableau F a ρ T q.horizon x.toLeaf i j)) ∧ Faint (purseP W) (spinR targetPower) (fun x=> coeff e ((bornM (ρ:=ρ) (T:=T) (W:=W) a q.horizon x.a x.top x.b)⁻¹ i j)-coeff e ((tableau F a ρ T q.horizon x.toLeaf)⁻¹ i j)):= by
   let τ:=purseP W
   have hv (U:X→ℕ→ℕ→ℝ)(V: Leaf W.scrolls→ℝ)(h:∀ x, Ends (fun n=>U x.a (seqN x n) x.b) (V x)) (he:Pact τ (spinR targetPower) (fun x=>U x.a x.top x.b) (fun x=>U x.a x.summit x.b)) : Faint τ (spinR targetPower) (fun x=>U x.a x.top x.b-V x.toLeaf) := by
       obtain ⟨C,⟨B,n,u,H⟩,c,Z⟩:= he.blur; let f x:= B*τ.day x^n; have hf x:0≤ f x:= mul_nonneg u (pow_nonneg (τ.good _) n); refine ⟨_,(soft_coin τ B).times ((soft_day τ).pows n), hf, fun x=>?_⟩; apply le_of_tendsto (continuous_abs.continuousAt.tendsto.comp (tendsto_const_nhds.sub (h x.toLeaf))); filter_upwards [eventually_ge_atTop x.top] with i hi; let y:transferPoint W:=⟨x.toLeaf,x.top,seqN x.toLeaf i,x.wing,(by unfold seqN;omega)⟩; exact (Z y).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (H y)) (ratioR_pos ..).le)
   exact ⟨hv (fun x m n=>coeff e (bornM (ρ:=ρ) (T:=T) (W:=W) _ q.horizon x m n i j)) _ (fun x=> orig q u h a hs ht hb hr x i j he) (Elm.staccato q u h hs ht hb a hr i j e he), hv (fun x m n=>coeff e ((bornM (ρ:=ρ) (T:=T) (W:=W) _ q.horizon x m n)⁻¹ i j)) _ (fun x=> quietP (coinD x) (coinP x) (staticBack q u h a hs ht hb hr x i j _ he)) (runwayBack q u h a hs ht hb hr _ _ e he)⟩
end YM.FormalBulk08.Trellis
