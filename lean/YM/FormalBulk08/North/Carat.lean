import YM.FormalBulk08.North.Glow

/-! Calendar's local overlapping steps at infinite top. Prescribed flat
row limits. These are on the cover, not finite-regulator substitutions. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.North
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I J:Type}{G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{E e:ℕ}{W:Lab G K I}
-- inserted static index at fixed i to justify address

def MeanP (W:Lab G K I)(x:I)(i N:ℕ): Row (Lodge.selected G ((W.V x).clock.op i 0).patch (W.wood x i)) (Loc G 1) := locating G K (destination (W.V x) N i) (W.wood x i)
def CovP (W:Lab G K I)(x:I)(i N:ℕ): Row (Lodge.selected G ((W.V x).clock.op i 0).patch (W.wood x i)) (Lodge.selected G ((W.V x).clock.op i 0).patch (W.wood x i)):= Flat.gamma G K (destination (W.V x) N i) (W.wood x i) (W.toEmpire.bill x i)
def Mean (W:Lab G K I)(x:I)(i:ℕ):= terminalR (MeanP W x i)
def Cov (W:Lab G K I)(x:I)(i:ℕ):= terminalR (CovP W x i)
structure Pace {I J:Type} (σ C:ℝ)(U:ℕ→ℝ)(f:ℕ→ Row I J)(T:Row I J)(m:ℕ):Prop where
   stays: ∀ N,m<N→ (f N).strip σ C
   moves: ∀ i j v,Ends (fun N=>f N i j v) (T i j v)
   value:T.strip σ C
   price:∀ N,m<N→(minusRows (f N) T).strip σ (U N)
lemma pacer {σ C:ℝ} (f:ℕ→Row I J)(U:ℕ→ℝ)(h:0≤σ)(hx:Ends U 0)(m:ℕ)(he:∀ N,m<N→ (f N).strip σ C)(ht:∀ N M,m<N→ N≤M→ (minusRows (f N) (f M)).strip σ (U N)): Pace σ C U f (terminalR f) m:= by
   have hp:= eventually_gt_atTop m; have hh:= row_aura h hx (hp.mono (show ∀ n,m<n → ∀ M,n≤M → (minusRows (f n) (f M)).strip σ (U n) from fun n hn M hm=> ht n M hn hm))
   exact ⟨he,hh,fun i j=> linger (hh i j) (hp.mono fun N h=>he N h i j),fun N h=>row_shiver (n:=N) hh (fun M hm=> ht N M h hm)⟩
variable (h:Use W ρ E)(x:Leaf W.scrolls)
include h
def levy (x:Leaf W.scrolls) (ρ:ChartRatio G)(E N:ℕ):= W.callL x ρ E * fare_n (stageFoot _ x 1) N
lemma ongoing : Pace (W.windowD x) (W.callL x ρ E) (levy x ρ E) (MeanP W x.a x.b) (Mean W x.a x.b) x.b ∧ Pace (W.windowD x) (W.callL x ρ E) (levy x ρ E) (CovP W x.a x.b) (Cov W x.a x.b) x.b := by
     have hu N M (p:x.b<N)(e:N≤M):= (W.turn_whose h x).goods (W.V x.a) _ N M p e rfl rfl (W.toEmpire.bill x.a x.b); have ht:0≤W.windowD x:=(h.zero x).le; have he:Ends (levy x ρ E) 0:= fare_fin_lt (stageFoot _ x 1) _
     exact ⟨pacer (MeanP W x.a x.b) _ ht he x.b (fun i hi=>(hu i i hi le_rfl).mean) (fun i j p e=> (hu i j p e).bend), pacer (CovP W x.a x.b) _ ht he x.b (fun i hi=> (hu i i hi le_rfl).single) (fun i j p e=>(hu i j p e).line)⟩
omit h in
lemma pace_split {σ C:ℝ}{U:ℕ→ℝ}{f:ℕ→Row I J}{T:Row I J}{m:ℕ}(h:Pace σ C U f T m): ∀ N,m<N→ (minusRows (f N) T).strip σ (U N):=h.price
-- use Totem transforms at fixed x, time NONE = constant bounded. Need tooling Float.
end YM.FormalBulk08.North
