import YM.FormalBulk08.Castor.Tote
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Castor
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G: Gauge}{K:KernelChoices}{I X:Type}{W:Lab G K X}{ρ:ChartRatio G}{d E R m D e r:ℕ}{B:Frame G d}{Z:Frame G m}{o:Loc G 1}{P:SectionData B}{T:SectionData Z}{H:Hol G}
variable (h:Quota B H W o D E R)(q:Quota Z H W o D E R)(u:Use W ρ E)(v:LocalRatio ρ) (a:hue G)(hg:G.Simple)(hp:P.Sound H)(hK:Bid.pop P)(ht:T.Sound H)(hb:Bid.pop T)(hk:m≤ d)(hr:d≤R)
include h q u v a hg hp hK ht hb hk hr
lemma voyageR (C: Pin W.scrolls) (i:Letter Z)(he:e≤ E)(r): Tender (sage C) o W.eagle (Degree targetPower) (fun x p=> peelR (ρ:=ρ) h q a x.a (C.N x.a) x.b P T i p e r):= by
    by_cases hw:r≤e+Pose.slots Z i; exact succinct h q u v a hg hp hK ht hb hk hr C i e r he hw
    have hh (x:Deck C):= (canopy_nav (birth a v h hg hp hK x.a x.b (C.N x.a) x.zone x.cap) ((birth a v q hg ht hb x.a x.b (C.N x.a) x.zone x.cap).officers i)).1.fare
    simp_rw [show ∀ x:Deck C,∀ p, peelR (ρ:=ρ) h q a x.a (C.N x.a) x.b P T i p e r=0 from fun x p=>Classical.byContradiction fun hv=> hw (Nat.add_comm e (Pose.slots Z i) ▸ (hh x).1 p e r hv)]; exact bear_void ..
lemma penny_mesh (i: Letter Z)(he:e≤ E)(r): Tender (aurum W) o (fun x=> W.width x.a x.b) (purseR targetPower) (fun x p=> peelR (ρ:=ρ) h q a x.a x.top x.b P T i p e r):= tenderLift (p:= Lab.meshPoint.role (W:=W)) (soft_day (aurum W)) (voyageR (h.shift Test.x) (q.shift Test.x) (Lab.observed W u _) v a hg hp hK ht hb hk hr (Lab.Test.ND W) i he r)

-- compatibility through ANY ℓ, episode.
variable (x:Leaf W.scrolls)
lemma snowRank (i: Letter Z) (he:e≤E) (r)(p:Studio D): Boone (fun n=> peelR (ρ:=ρ) h q a x.a (n+x.b) x.b P T i p e r) 0:= by
    let g (n:ℕ):meshPoint W:= ⟨x,n+x.b,n+x.b,by omega,le_rfl⟩
    have he:= penny_mesh h q u v a hg hp hK ht hb hk hr i he r; obtain ⟨B,b,k,H⟩:= tenderLift (p:=g) (show Soft staticT _ from soft_coin _ ((chron _).day x)) he
    let δ(n:ℕ) := fare_n x (n+x.b); let S(n:ℕ):= peelR (ρ:=ρ) h q a x.a (n+x.b) x.b P T i p e r
    refine ⟨fun w=> quietude (δ:=δ) ((tendsto_add_atTop_iff_nat _).mpr (fare_fin x)) (fun i=> (ratioR_pos ..).le) ?H⟩; change Faint staticT δ (fun i=> S i w); refine ⟨_,b.times (soft_coin staticT ‖p‖),fun i=>mul_nonneg (k i) (norm_nonneg _),fun i=>?_⟩; refine le_trans (cool (H i p) (u.zero x).le w) (le_of_eq ?_); change B i*(δ i*_) = _; ring

def GateM (W:Lab G K X)(a:hue G)(ρ:ChartRatio G)(F':Frame G d)(Z':Frame G m)(T:SectionData Z')(h:m+1≤D)(x:Leaf W.scrolls) := pantry F' (issue W ρ a Z' T h x.a x.b)
omit h hp hK in
lemma swimG (j:Letter Z)(i:Letter B): Priced staticT (fun i=> fare_n x (i+x.b)) (fun n=> pantry B (bornY ρ W a Z T q.horizon x.a (n+x.b) x.b) i j) (fun _=> GateM W a ρ B Z T q.horizon x i j) E := mana (T:=fun n=> bornY ρ W a Z T q.horizon x.a (n+x.b) x.b j) B (fun _ ht' r=>pantry_prices q u v a hg ht hb (hk.trans hr) ht' j r x) (u.zero x) _
lemma nests (j:Letter Z)(p:Studio D)(he:e≤ E)(r): issue W ρ a Z T q.horizon x.a x.b j p e r=larch (issue W ρ a B P h.horizon x.a x.b) (GateM W a ρ B Z T q.horizon x) j p e r:= by
    let Y i:=bornY ρ W a Z T q.horizon x.a (i+x.b) x.b; let V i:=bornY ρ W a B P h.horizon x.a (i+x.b) x.b; let U:=issue W ρ a B P h.horizon x.a x.b; let R:=issue W ρ a Z T q.horizon x.a x.b; let g:=pantry B R;let G i:=pantry B (Y i)
    have hp': Brass staticT o (fun _=>W.windowD x) (fun i=>fare_n x (i+x.b)) (fun _=>1) (fun i p=> larch (V i) (G i) j p e r) (fun _ p=> larch U g j p e r):= orbit_match (T:=V) j (fun e hv r i=> pantry_prices h u v a hg hp hK hr hv i r x) (fun i=>swimG q u v a hg ht hb hk hr x j i) he
    have hz (n): Y n j= peelR (ρ:=ρ) h q a x.a (n+x.b) x.b P T j + larch (V n) (G n) j:= (sub_add_cancel (Y n j) _).symm
    have ht':= sarking hp' p (u.zero x).le ((tendsto_add_atTop_iff_nat _).mpr (fare_fin x)) (fun i=>(ratioR_pos ..).le); ext t; have he' : Ends (fun n=> Y n j p e r t) (issue W _ _ _ _ q.horizon x.a x.b j p e r t):= (tendsto_add_atTop_iff_nat x.b).mpr ((Drift.harbor q u v a hg ht hb (hk.trans hr) he j r x p).shares t)
    change _ = larch U g j p e r t; apply tendsto_nhds_unique he'
    have ht'':= ((snowRank h q u v a hg hp hK ht hb hk hr x j he r p).shares t).add (ht'.shares t); simp only [Pi.zero_apply,zero_add] at ht''; exact ht''.congr' (.of_forall fun n=>by dsimp only; rw [hz];rfl)
end YM.FormalBulk08.Castor
