import YM.FVA2.Embr.Signal
import YM.FVA2.Hearth.Route
import YM.FormalOPE.RG10.Gists.Roll
/-!
 # Connected marker program BEFORE any stopped step, and after a depth

 Preserve Marker namespace wherever evaluating power series in physical g. This
 is on the *regulator* with odd ratios and branches & all stamped choices,
 no estimate obtained by carrying independent guesses for each compound step.
 `Lumen.Fk.read` publishes each row from exactly these wires and whole `$Ω$`.
 Not conditioning the single insertions separately before forming their product.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Sync Route Gists Marker Extra.Trajectories
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{L':Type}{A0:Type}{n:Side} {L:Fabric G n}{T:Cloth L}{J:ChartRatio G}
open Arrival
variable (Y:XSpace.Initialize G)
local notation "O"=> PowerSeries ℝ
lemma buys (a:Folio G)(l:List (Folio G))(h:Even n.val) : markValue Y (a::l) n=markValue Y [a] n * markValue Y l n:= by
 let i:=Folio.asset [a]; let b:=Folio.asset l
 have H:Folio.asset (a::l) = i+b:= by simp only [i,b,Folio.asset,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
 suffices he:imprintRoot ( Folio.scenario Y n (a::l) )=imprintRoot ( Folio.scenario Y n [a]) * imprintRoot ( Folio.scenario Y n l) by
    rw [ ← Hearth.launching Y (a::l) h, ← Hearth.launching Y [a] h, ← Hearth.launching Y l h,H ] at he; have hZ:= show PowerSeries.X ^ (i+b)*markValue Y (a::l) n= PowerSeries.X ^ (i+b)*(markValue Y [a] n * markValue Y l n) from he.trans (by change PowerSeries.X^i*_*(PowerSeries.X^b*_)=_; rw [pow_add]; ring); rw [ ← Stack.drop_mul (i+b) (markValue Y (a::l) n),hZ,Stack.drop_mul ] -- avoid rw RHS pattern cycle
 let f:= Hearth.seed (Folio.scenario Y n [a]); let g:= Hearth.seed (Folio.scenario Y n l)
 let T:= localTruss (endcap (G:=G) n h); have he: Hearth.seed (Folio.scenario Y n (a::l))=f*g:= by simp only [f,g,Folio.scenario,Change.joints,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rfl
 change Stack.rise (Hearth.seed (Folio.scenario Y n (a::l)))=Stack.rise f* Stack.rise g; rw [he,Stack.rise_mul (Hearth.certified T _ (Folio.matured Y n [a] h)) (Hearth.certified T _ (Folio.matured Y n l h))]
abbrev Planar (k:Side)(G:Gauge) := Channel (Streets G k)
open Multi (Hot)
variable {I:Type}[Fintype I][DecidableEq I](R:Census I)

-- any positive-mode initial log data; e.g. the physical top stencils or more generally
-- prepared logs. Commission stays the same for all fields. 
def logway {n:Side}{L:Fabric G n}(T:Cloth L)(w:L.Cost→O)(B:Unmasked G n)(Z: Multi.Hot R→ Planar n G)(J:ChartRatio G)(h:Commission J T B w): Multi.Hot R→ Planar (Bottom L) G:= match T with
 | .floor _ _ _=>Z
 | .inLayer (c:=c) (t:=t) (L:=M) P C=> show Multi.Hot R→ Planar (Bottom M) G from
      let u:= Exists.choose h
      let A:= (Engine J t P (natural n G) (natural c G) (w none) B u)
      logway (L:=M) C (w∘some) (Update P t J (w none) B u) (fun q=> cumulLog A R Z q.val) J (Exists.choose_spec h)
lemma runUp {n:Side}{L:Fabric G n}(T:Cloth L)(w:L.Cost→O)(B:Unmasked G n)(Z:Multi.Hot R→ Planar n G)(J: ChartRatio G)(h:Commission J T B w) (s:R.Mode): Gists.program R (logway R T w B Z J h) s= Hearth.channelTransit T w B (Gists.program R Z s) J h:= by
 cases T with
 | floor=> rfl
 | @inLayer c f S H t hf L P C=>
     unfold logway Hearth.channelTransit; let u:= Exists.choose h; let A:= Engine J t P (natural n G) (natural c G) (w none) B u; let V:= fun v: Multi.Hot R=> cumulLog A R Z v.val
     exact (runUp C (w∘some) (Update P t J (w none) B u) V J (Exists.choose_spec h) s).trans (congr_arg (fun x=> Hearth.channelTransit C _ _ x J (Exists.choose_spec h)) (Gists.unfolds A R Z s).symm)
termination_by structural T

-- physical alphabet start: arbitrary finite stencils per slot, also merging already
-- favorable births (other observable choices by linearity in ticket). Emit encodes
-- ALL disjoint initial products together. Mark support exactly these names.
variable (Φ:I→ Folio G)
def mark (q:R.Mode) := q.val.toList.map Φ
local notation "T!"=> natural n G
def query (n:Side) (q:R.Mode): Planar n G:= Sync.digital (natural n G) (markValue Y (mark R Φ q) n)
local notation "B"=> query Y R Φ n
omit [Fintype I] in
lemma cleaner (t: Ticket (Flats G n)) : Stack.drop 0 t=t:=PowerSeries.ext (fun i=>by rw [Stack.drop,PowerSeries.coeff_mk,Nat.zero_add])
omit [Fintype I] in
lemma query_nil : B R.quiet=1:= by unfold query markValue mark; rw [show (List.map Φ (R.quiet.val.toList))=[] from by simp [Census.quiet]]; change digital T! (Stack.drop 0 (Stack.rise (1:Flats G n→ℝ)))=1; rw [Stack.rise_one,Embr.cleaner,map_one]
omit [Fintype I] in
lemma fidelity (s:R.Mode)(h:Even n.val): B s=∏ i∈ s.val, Sync.digital T! (markValue Y [Φ i] n):= by
 have hx (l:List I): markValue Y (List.map Φ l) n= (List.map (fun i=> markValue Y [Φ i] n) l).prod := by
    induction l with
    | nil=> change Stack.drop 0 (Stack.rise (1:Flats G n→ℝ))=1; rw [Stack.rise_one,Embr.cleaner]
    | cons x xs ih=> exact (buys Y _ _ h).trans (congr_arg (markValue Y [Φ x] n * ·) ih)
 unfold query mark; rw [hx,map_list_prod]; simp
-- seed log: on this exact lattice, not constructing ANY approximation to the density
-- through a chosen order. Full-series compatibility at all budgets.
def beginOn (n:Side)(u:Multi.Hot R): Planar n G:= Card.logRow R (query Y R Φ n) u.val
local notation "M"=> beginOn Y R Φ n
lemma began (x:Streets G n→ℂ)(h:Even n.val): Gists.dramatize R M x=FormalOPE.RG10.Word.logWord (FormalOPE.RG10.Word.emit R (fun i=> Route.run x (Sync.digital T! (markValue Y [Φ i] n)))):= by rw [show M= (fun u: Multi.Hot R=> Card.logRow R B u.val) from rfl, Gists.Card.foremost R B x (query_nil Y R Φ) ]; apply congr_arg; apply FormalOPE.RG10.Word.observe_ext; intro i; rw [Gists.seen, Word.emit_part, fidelity Y R Φ i h,map_prod]

variable (T)(z:L.Accounts→ O)(hz:∀ i,0<term (z i) 0)(hj:LocalRatio J)
local notation "Z"=> Facade.headquarters z
local notation "T₀"=> collared T z hj hz
local notation "W"=> logway R T (z∘some) Z M J T₀
local notation "Y₀"=> natural (Bottom L) G

def observed (q:R.Mode)(y: Flats G (Bottom L)) := Sync.align (Stack.read y ( Facade.drive T (z∘some) Z (markValue Y (mark R Φ q) n) J T₀).2)
lemma kernelTransmit (q:R.Mode) : Gists.program R W q= Sync.digital Y₀ ( Facade.drive T (z∘some) Z (markValue Y (mark R Φ q) n) J T₀).2:= (runUp R T _ Z M J T₀ q).trans (by rw [show Gists.program R M q= B q from Gists.Card.moment_law R B q (query_nil Y R Φ)]; exact centeredTransit T _ _ _ T₀ hj (OpenSlots.restores ..))
variable (y: Flats G (Bottom L))
local notation "F"=> Sync.tint Y₀ y
lemma reported (q:R.Mode) : observed T Y R Φ z hz hj q y= run F (Gists.program R W q):= by rw [kernelTransmit (hj:=hj) (hz:=hz),Sync.accessing]; rfl
local notation "WA"=> FormalOPE.RG10.Word.package (fun s:R.Mode=> observed T Y R Φ z hz hj s y)
lemma walker : FormalOPE.RG10.Word.logWord WA= Gists.dramatize R W F:= by
 rw [←FormalOPE.RG10.Word.log_exp (Gists.dramatize R W F) (Gists.under ..), Gists.plotting]; unfold Gists.seeOrd; apply congr_arg; apply congr_arg; funext q; rw [reported]
end YM.FVA2.Embr
