import YM.WilsonCoeffUV.Marked.Paths.Purchase
import YM.WilsonCoeffUV.Root.UV.TVPrice
/-!
# Mark read barrier in publication units. Aligned representatives for core ε
 Comparison stronger: normalized single source across cutoff chain; unmarked
 elsewhere. Port used after input budgets at SAME Sector.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Cadenza
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost Mer.Rolls
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Polestar Ticket Flooring
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {c f:Side}{ι U V:Type}{J I S:Finset ι}{i j i' D a e r h k N n m b l B':ℕ}{G:Gauge}{s c' σ τ u g A B C z ρ:ℝ}{E W W' V' U':Credit}

lemma vatic {P F:Bookend (Vote D) G}(h:Mer.Rolls.Nimbus k (e+1) F)(p:Mer.Rolls.Nimbus k (e+1) P)
     (a:Rain P (e+1) s A)(t:Rain F (e+1) s A)(b:Rain (P-F) (e+1) s B)(v:Stigmata G l r (e+1) s c' u)(x:k≤r)(hp:i≤ e+1):
     Rains (automa P k i) i c' (u*A) ∧ Rains (automa F k i) i c' (u*A) ∧ Rains (automa (P-F) k i) i c' (u*B) ∧ Vista (automa F k i) (automa (P-F) k i) (automa P k i) i ∧
     (∀ j< i,(baton (automa F k i) i).2 j=F j) ∧ (∀ j< i,(baton (automa P k i) i).2 j=P j):=by
    have he:= v.singles P k i A x hp p a; have ht:= v.singles F k i A x hp h t; have hb:=twilit p h
    refine ⟨he.1,ht.1,(v.singles (P-F) k i B x hp hb b).1,?_,ht.2,he.2⟩
    have hf:= looping F (P-F) h hb t b i hp hp v.original v.original; rw [add_sub_cancel] at hf; exact hf
variable {H:Hol G}{R:Realm G (e+1) E}{Q:SealR G}
lemma recital (s:Origin R H W V' Q)(p:Insure b k R W')(X: Alma Q.F)(x:valence Q.F X≤k)(v:R.anchor≤m)(hn:m≤ N)(q:i≤e+1):
    let F:= (glory R.draws R.paid Q.ans Q.path m) X; let P:= (Peaks R.draws R.paid Q.ans Q.path N m).2 X
    let k':= valence Q.F X; let t:= VestS b k R m v; let A:= R.cash (W'.prodC (allPlays H Q.ans Q.path e E W).choose) m; let B:=A*R.tempC m N
    Rains (automa P k' i) i t A∧ Rains (automa F k' i) i t A∧ Rains (automa (P-F) k' i) i t B∧ Vista (automa F k' i) (automa (P-F) k' i) (automa P k' i) i∧
    (∀ j< i,(baton (automa F k' i) i).2 j=F j) ∧ (∀ j< i,(baton (automa P k' i) i).2 j=P j):=by
    intro F P k' t A B
    let L:= s.prest.f.arch; have hv:= s.width m v; have he:L.V.draws=R.draws:= s.prest.lands; have hh:L.V.anchor ≤ m:= s.prest.tap.symm ▸ v; have hd:L.V.paid=R.paid:= s.prest.modes; have hw:P=(L.lore N m).2 X:=by change _=(Peaks _ _ _ _ N m).2 X; rw [he,hd]
    have hu:F=L.matron m X:=by change _=glory _ _ _ _ m X; rw [he,hd]
    have hP: Mer.Rolls.Nimbus k' (e+1) P:= by
        let T:= ((fun n=>(L.lore N m).1 n X),(L.lore N m).2 X); have hx: Auth k' T:= On_auth ((production L hn hh).1.scan.solo _)
        rw [hw]; exact nimb _ hx _
    have hF: Mer.Rolls.Nimbus k' (e+1) F:=by rw [hu]; let Z:= primetime L hh; exact ⟨fun i hi=> Z.cure _ _ (by omega),fun i hi j hj=> Z.trim _ _ _ (by omega) hj, fun i hi=> Z.work _ _ (by omega),fun i hi j=> Z.slick _ _ _ (by omega)⟩
    let u:= (allPlays H Q.ans Q.path e E W).choose; let C:=R.cash u m; let m':= Vσ R m v; let δ:= R.tempC m N
    have hx j (w:j≤ e) r: Shelf Bank.terrain 0 m' C δ (P j r) (F j r):=by
        rw [hw,hu]; have hg:= cheers (N:=N) (m:=m) L ((allPlays H Q.ans Q.path e E W).choose_spec j _ r w) hh hn le_rfl X rfl; rw [show L.V.cash u m=R.cash u m from congr_arg (fun s:ℕ→ℝ=>u.buy (s m)) s.prest.depths, show L.V.tempC m N=R.tempC m N from congr_arg (fun s:Levels G=>trailC s.S m N) he] at hg; exact hg.shrink ((min_le_right ..).trans hv)
    have hz:0≤C:=zero_le_one.trans (Credit.purchase _ (R.depth m v)); have hδ:0≤δ:= (trail_pos ..).le
    have hg:= p.proof m v; obtain ⟨a,b',c,d,e,f⟩:= vatic hF hP (s:=m') ⟨hz,fun j p r=> (hx j (by omega) r).wax⟩ ⟨hz,fun j p r=>(hx j (by omega) r).wane⟩ ⟨mul_nonneg hz hδ,fun j p r=> (hx j (by omega) r).toll⟩ hg x q
    have h': VestZ b k R m v * C ≤ A:=by unfold A cash; rw [Credit.products]; exact mul_le_mul_of_nonneg_right (p.labor m v).2 hz
    exact ⟨a.slack le_rfl h',b'.slack le_rfl h', c.slack le_rfl ((show _= VestZ b k R m v * C*δ from (mul_assoc ..).symm).le.trans (mul_le_mul_of_nonneg_right h' hδ)),d,e,f⟩
end YM.WilsonCoeffUV.Wheel.Cadenza
