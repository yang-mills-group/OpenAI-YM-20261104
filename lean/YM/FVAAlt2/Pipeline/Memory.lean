import YM.FVAAlt2.Pipeline.Film
/-! # Pack.Cover.V old Reader formula shadows **every Run.World program** at period p exactly. Ler.period states.Tensor.C.Init of Scout, depth=m.Begin.Describe Profile.Y.Observer. No winding repayment here: also yields formulas for costs later (performed entirely on the finite BUS diagrams state with profile budget).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm Marker Multi
open PowerSeries
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {m :ℕ} {G:Gauge} {R X:Type} [DecidableEq R] {Q:KernelChoices} {M:X→ℕ} {N:Page M→Side}
open Oracle Period.Field
variable (C:Circuit M N) (Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (Γ: History G)(K: Bulk.Chain Γ)(P: Period.Field.SeriesT C Q Γ)
variable (S: Marker.Census R)(u:R) (A: X→ Boot.Scout (G:=G) m)
variable (L:Page M→ Binding.Scale)
variable (p:ℕ) -- period
namespace See
variable {C Γ}
local notation:max "x_" k:max=> P.vol k
set_option quotPrecheck false
local notation:max "f_" k:max => (Γ.S.side (P.vol k) p)
local notation:max "U_" k:max => P.stepData C Γ p k
local notation:max "F_" k:max => Halo.bios ( P.stepData C Γ p k )
local notation:max "P_" k:max => P.records C Γ p k
local notation:max "J_" k:max => directive (P.stepData C Γ p k)
local notation:max "K_" k:max => ( P.readyKin C Γ K p k )
local notation:max "w_" k:max=> Page.opening M k
local notation:max "B_" k:max=> ( Boot.ink S u Γ (P.vol (w_ k)) p (A k) )
-- Reader constructor
abbrev StockT (x:Page M):=Orders (Pin (f_ x) G)
abbrev Adapt :Type:= ∀ i:Page M, StockT P p i
local notation:max "M_" x:max => ( Circuit.mural G L x )
local notation:max "Z_" x:max => C.bore G Φ L x
local notation:max "V_" z:max => Arm.scriptV (U_ z) (F_ z) (K_ z) ( C.bore G Φ L z )
abbrev Recv (i:Flap M) (u:StockT P p i.prev): Orders (Pin (Γ.S.side (P.vol i.next+1) p) G):= castF (X:=fun i=>Orders (Pin (Γ.S.side i p) G)) (P.links i) u
abbrev riseV (i:Flap M)(u:StockT P p i.prev): StockT P p i.next:= Arm.OutputV (U_ i) (F_ i) (K_ i) ( C.bore G Φ L i ) (Recv P p i u)
abbrev riseM (i:Flap M)(m:ℕ)(u v:StockT P p i.prev): StockT P p i.next:= Arm.OutputM (U_ i) (F_ i) (K_ i) (C.bore G Φ L i) (Recv P p i u) (Recv P p i v) m
lemma poster_h (i:Flap M) : Sphere (U_ i) (F_ i) (L i.prev) ( Z_ i ):=by
    have hx:(U_ i).patch=(C.rail Q i).patch:= P.pact i p
    have h:=(C.wheeled G Φ L i); unfold Sphere at h ⊢; intro j; rw [Older.neverP (U_ i) (C.rail Q i) hx ( P.creed i p )]; apply h

def work : Adapt P p:= Halo.seriesC (fun k=> Boot.weights M_ k (f_ (w_ k))) (riseV Φ K P L p)
def observe : Adapt P p:= Halo.seriesC (fun k=> Boot.view (A k) (f_ (w_ k))) (fun i=> riseM Φ K P L p i m (work Φ K P L p i.prev) )
local notation "Z"=> work Φ K P L p
local notation "W"=> observe Φ K P A L p
lemma itinerary (k:Flap M): Z k.next = riseV Φ K P L p k (Z (Flap.prev k)):=Halo.laterC _
lemma display (k:Flap M): W k.next = riseM Φ K P L p k m (Z (Flap.prev k)) (W (Flap.prev k)):=Halo.laterC _
variable (r:ℕ)(T:Times (L:=L) r)[Fintype R]
local notation:max "t_" i:max => T.cloth i
local notation:max "Z₀" k:max=> Recv P p k (Z (Flap.prev k))
-- warning notation application. use e.g. `Z₀ k`
local notation:max "W₀" k:max=> Recv P p k (W (Flap.prev k))
def Able (m:ℕ) (f:Side)(y:Colors S G f): Prop:= Well y ∧ y.power (Arm.pub u)=m
def Prepared (i:Page M)(y:Colors S G (Γ.S.side (P.vol i) p)):Prop:= Arm.Simmer (P_ i).clip (P_ i).path (t_ i) y ( Z i ) r ∧ Arm.Single (t_ i) y (W i) u r m ∧ y.power (Arm.pub u)=m
local notation "R!"=> Prepared Φ K P S u A L p r T
variable (hL:∀ i:X,L (Page.opening M i)=Clocks.flat)
include hL
lemma starts (x:X): R! ( Page.opening M x ) ( Boot.ink S u Γ (P.vol (Page.opening M x)) p (A x) ):= by
    let g:= Page.opening M x; have hm:= Circuit.serene G L x; rw [hL] at hm; unfold Prepared; rw [T.top]; exact ⟨Boot.payable S u Γ K _ p (A x) M_ x hm r,Boot.singles S u Γ (P.vol g) p (A x) r,rfl⟩
omit hL
-- cast across relation, no β covariance changes. Keep `K∼B` prior actual. read uses Θ.W throughout all. posture future q-local.
variable (i:Flap M)(y: Colors S G ( Γ.S.side (P.vol i.prev) p ))(y': Colors S G (Γ.S.side (P.vol i.next) p))
local notation "p₁"=> ( P_ i.next )
local notation "p'"=> Γ.rep (P.start C Γ i.volW) p (P.vol i.next+1)
local notation "y₀"=> before P i y
variable (h:Prepared Φ K P S u A L p r T i.prev y)
include h
lemma progressed : Arm.Simmer (p').clip (p').path ( t_ i.prev ) (y₀) ( Z₀ i ) r ∧ Arm.Single ( t_ i.prev ) (y₀) ( W₀ i ) u r m ∧ ( before P i y ).power ( Arm.pub u ) = m:=by
    refine ⟨?_,?_,?_ ⟩
    · refine transferred (X:=fun i=> Colors S G (Γ.S.side i p)) (Y:=fun i=>Orders (Pin (Γ.S.side i p) G)) (fun j y a=> Arm.Simmer (Γ.rep (P.start C Γ i.volW) p j).clip (Γ.rep (P.start C Γ i.volW) p j).path (t_ i.prev) y a r) y (Z i.prev) (P.links i) h.1
    · exact transferred (X:=fun i=> Colors S G (Γ.S.side i p)) (Y:=fun i=>Orders (Pin (Γ.S.side i p) G)) (fun _ x z=> Arm.Single (t_ i.prev) x z u r m) y (W i.prev) (P.links i) h.2.1
    exact See.poster (fun j a=> (show Colors S G (Γ.S.side j p) from a).power ( Arm.pub u ) = m) y (P.links i) h.2.2 -- infer type
local notation "B"=> C.tables Y i.prev
include Y -- retain h
lemma litV : Uniforms.Bright (Z i.next) (p₁).path (p₁).clip r:=by
    obtain ⟨hv,hp,he⟩:=progressed Φ K P S u A L p r T i y h; rw [itinerary]; exact Uniforms.clear (U_ i) (F_ i) (L i.prev) (K_ i) ( t_ i.prev ) (Geometry.Field.Square.proper _ _) (Z_ i) (Z₀ i) (before P i y) r ( T.holds i.prev ) (poster_h Φ P L p i) hv (Γ.levels.budget (P.vol i.next+1)) B (P.upstream Y C Γ K p i) (Thermal.maps K (P.start C Γ i.volW) (P.vol i.next) p (P.fresh C Γ i) _ _)
lemma litW : Uniforms.Glyph ( W i.next ) r m:=by
    obtain ⟨hv,hp,he⟩:=progressed Φ K P S u A L p r T i y h; rw [display]; exact Uniforms.upright (U_ i) (F_ i) (L i.prev) (K_ i) ( t_ i.prev ) (Geometry.Field.Square.proper _ _) (Z_ i) (Z₀ i) (W₀ i) y₀ r (T.holds i.prev) (poster_h Φ P L p i) hv (Γ.levels.budget (P.vol i.prev)) B (P.upstream Y C Γ K p i) m u hp he
-- constructors. causal.Se.Advancement with executable operator.
end See
end YM.RegulatorIR.FVAAlt2.Pipeline
