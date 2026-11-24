import YM.RegulatorIR.Halo.Wall

/-!
# Extension at fixed original list – power budgets on rows and singular count
Transfer NOT across this new period; emulate a batch at each original step. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Sight Uniform
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge} {W:Type}{M:W→ℕ}{n:Page M→Side}
variable {S: Heir n G} (H:Reel S)
namespace Aug
variable (w:W) {e k a q:ℕ} (p:S.Accounts)

-- part of primitive costs. target context $Λ$ not needed for this analysis:
-- point measurements at fixed w, only uniform over **Aux** extended horizons.
structure Amenities (S:Heir n G)(L:Meter W)(q k:ℕ):Prop where
 line : Beam (flapL M L) (S.ceilingRoom.cone k) S.lifts.lineL
 mean : Beam (flapL M L) (S.ceilingRoom.cone k) S.lifts.forecast
 budget : ∀ i ≤ q,∀ j,Workday (flapL M L) (S.ceilingRoom.cone k) fun w=> S.lifts.rails w i j

def sheet (k:ℕ) (h:k≤M w)(z:Side):Page (extent M w):= ⟨z,k,h⟩
def stepf (k:ℕ)(h:k<M w)(z:Side): Flap (extent M w):= ⟨z,k,h⟩
local notation "E" => eternal H w

def known (j:ℕ)(h:j<M w): Batch (fun _:Side=>Foot G) (fun _:Side=>Foot G) (fun z=>Book G (big w (n:=n) ((stepf w j h z).prev))) (fun z=>Book G (big w (n:=n) ((stepf w j h z).next))) := {
 period:= width (S:=S) w
 positive:= fun z=> (E).hp z
 fine:=fun z=>(E).maps ((stepf w j h z).prev)
 coarse:=fun z=>(E).maps ((stepf w j h z).next)
 grid:=fun z=>stations H w (stepf w j h z) }

def light :Meter Side:= { val:=fun _=>1, above:=fun _=>le_rfl,below:=fun _=>ENNReal.one_ne_top }

def lpost (j:ℕ)(t:j≤ M w):Post (fun _:Side=>Foot G) (fun z=>Book G (big w n (sheet w j t z))) := { period:= (E).P,positive:=(E).hp,length:= fun z=> (E).l (sheet w j t z),spacing:=fun z=> (E).hl (sheet w j t z),deck:=fun z=>radar H w (sheet w j t z) }
abbrev delay (j:ℕ) (h:j<M w) := S.l (Page.mk w (j+1) h)

-- joint layer prices transfer along all repetitions at one fixed step.
variable {L:Meter W}(T : Amenities S L q k) (B:S.Supplies p L q k) (j:ℕ)(h:j<M w)
local notation "F" => known H w j h
local notation "l" => delay (S:=S) w j h
local notation "Q" => Batch.insideRoom F (fun _=>l) (fun _=>Sky.hl S _)
local notation "U" => Batch.incoming F (fun _=>l) (fun _=>Sky.hl S _)
lemma cost_r (z:Side)(a:ℕ): (Q).cone a z= S.ceilingRoom.cone a (⟨w,j,h⟩: Flap M):=by
 let i :Flap M:= ⟨w,j,h⟩
 let lq:=S.ceiling i; let x:=Step.combine (S.maps i.prev) (S.maps i.next)
 change _=(Tariff.native lq _ a).uses x.pos; unfold x; rw [H.realms i.prev,H.realms i.next];rfl
lemma cost_f (z:Side)(a:ℕ) : (U).cone a z= S.bar.cone a (⟨w,j,h⟩:Flap M):=by
 let i:Flap M:= ⟨w,j,h⟩
 change _= (Tariff.native (S.ceiling i) _ a).uses (S.maps i.prev).pos
 rw [H.realms]; rfl
include T
lemma beams : Beam light ((Q).cone k) (F).lineL:=by
 obtain ⟨c,hc,Y⟩:= T.line; let v:Flap M:=⟨w,j,h⟩
 refine ⟨_,Poly.standard _ (hc.cost v),fun z=>?_⟩
 rw [cost_r H]; exact Y v
lemma spurs : Beam light ((Q).cone k) (F).forecast:= by
 obtain ⟨c,hc,Y⟩:= T.mean; let v:Flap M:=⟨w,j,h⟩; refine ⟨_,Poly.standard _ (hc.cost v),fun z=>?_⟩; rw [cost_r H]; exact Y v
lemma added {e i:ℕ}(hp:e≤q): Workday light ((Q).cone k) fun z=>(F).rails z e i:=by
 obtain ⟨c,hc,Y⟩:=T.budget _ hp i;let v:Flap M:=⟨w,j,h⟩; refine ⟨_,Poly.standard _ (hc.cost v),fun z=>?_⟩; rw [cost_r H]; exact Y v
omit T in
lemma fete : Poly light ((Q).weight 6) := by
 let L' (z:Side):= (E).l (sheet w j h.le z)
 let i:Flap M:=⟨w,j,h⟩
 let g(z:Side):= (stepf w j h z)
 exact Geometry.sum_weight G.ColorIndex ((E).hp) (fun z=> (E).hl (g z).prev) (fun z=> (E).hl (g z).next) (fun z=> (E).hl (g z).next) (fun z=> Sight.context H w (g z).prev) (fun z=> Sight.context H w (g z).next) (fun z=>Sight.refined H w (g z).prev) (fun z=> Sight.refined H w (g z).next) (Poly.standard light (show ENNReal.ofReal (S.ceiling i/S.l i.prev)≠ ⊤ from ENNReal.ofReal_ne_top)) (Poly.standard light (show ENNReal.ofReal (S.ceiling i/S.ceiling i) ≠⊤ from ENNReal.ofReal_ne_top))
include B
omit T in
lemma conflict {e r:ℕ}(he:e≤q) : Workday light ((U).cone k) fun b=>(tele H p w).bulk ((stepf w j h b).prev) e r:=by
 obtain ⟨f,hx,hc⟩:= p.deposit B e he r
 let v:Flap M:=⟨w,j,h⟩; refine ⟨_,Poly.standard _ (hx.cost v),fun z=>?_⟩; rw [cost_f]; exact hc v
end Aug
end YM.RegulatorIR.Halo
