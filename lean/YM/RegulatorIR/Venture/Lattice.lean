import YM.RegulatorIR.Venture.Prism

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Venture
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
open Epoch VacDay
/-! Clock-free obligations for the Vacuum. Check by upcoming assembly
for a chancellor/chosen Ly, not assumed for assigned endpoint. -/
open Epoch.League
variable {X I: Type}{M:X→ℕ}{n:Page M→Side} {K : KernelChoices}
variable (S:Circuit M n)(Y:Program K)(G:Gauge)
variable (Z:∀ P:Patch,P.Branches K G)
-- scope. Measures required kernel tape to see
variable {p u r e:ℕ}
local notation "T₁"=> S.J
local notation "L"=> S.l

def curtain (i:Flap M):= ruling (S.pactP i) G (S.tells Y i)
def pathL (i:Flap M):= phiQ (S.pactP i) K (S.tells Y i) G
local notation "Z₁"=> curtain S Y G
local notation "Z₂"=> pathL S Y G
-- stable Merit; ornaments are coarser bore layer and B.cost.Yi poly required

def spoolA (u:ℕ)(i:Flap M):ℝ≥0∞:= Oracle.brick (S.pactP i) G (Y.receipt.Ω (S.J i.prev))*ENNReal.ofReal (scar (Y.receipt.α (S.J i.prev)) u)
def spoolB (u:ℕ)(i:Flap M):ℝ≥0∞:= Oracle.tariffJ (S.pactP i) K G (Y.receipt.Ω (S.J i.prev)) (Y.receipt.α (S.J i.prev)) u

def lnk (u:ℕ)(i:Page M): Tariff (Foot G):= path (S.l_p i) _ u
def drifted (u:ℕ)(i:Flap M):Tariff (KFoot G):= (Tariff.native (L i.next) (S.l_p i.next) u).uses (peak_o G (L i.prev) (L i.next))
local notation "M₁"=> lnk S G
local notation "M₂"=> drifted S G
lemma spooled (u i) : spoolA S Y G u i≠⊤∧spoolB S Y G u i≠⊤:=⟨by unfold spoolA brick;finiteness,tariffJ_f _ _ _ _⟩ -- namespaces argument
lemma merited (u i): Skein.Merit (Z₁ i) (Z₂ i) (Tariff.native (S.l i.next) (S.l_p i.next) u) (S.l i.prev) (fm G (S.l i.next)) (spoolA S Y G u i) (spoolB S Y G u i):=by
 let Z:= S.pactP i
 let X:= S.honored Y i.prev;let V:= S.predicted Y i;let T:= (Y.receipt.α (T₁ i.prev));let R:=Y.receipt.Ω (T₁ i.prev)
 let c:= scar T u; have hx:= (scars T u X.card.pos).2
 have h:= saves Z G _ V.rows X.card.paid; have hk:= buoys Z K G _ V.rows X.card.paid X.card.pos
 have hp:Z.L=S.sizeL i:=rfl; have he:S.l i.next=S.l i.prev* Z.L.val:= S.width_s i
 refine ⟨?_,?_⟩
 · exact ⟨ Oracle.payUp (V:=Oracle.fm G (S.l i.prev)) (U:= Oracle.fm G (S.l i.next)) (S.l_p i.next) c hx (costsB (S.l_p i.prev) he) (costsG (S.l_p _)) h.1, Oracle.payUp (U:=fm G (S.l i.prev)) (V:=fm G (S.l i.next)) (S.l_p i.next) c hx (costsG (S.l_p _)) (costsB (S.l_p _) he) h.2⟩
 exact ⟨Oracle.payUp (S.l_p i.next) c hx (costsC Z (S.l_p i.prev) he) (costsG (S.l_p _)) hk.1, Oracle.payUp (S.l_p i.next) c hx (costsG (S.l_p _)) (costsC Z (S.l_p _) he) hk.2⟩
def t_budget (u r:ℕ) (i:Flap M): ℝ≥0∞:= fore_c G.ColorIndex r u (5-(r+1)) (beginsP G S u Y i) * award (S.sizeL i).val
def sp_budget (u r:ℕ)(i:Flap M):ℝ≥0∞:= fore_b G.ColorIndex r u (5-(r+1)) (beginsP G S u Y i)*(↑(S.sizeL i).val:ℝ≥0∞)^4
-- structural readiness.Not projection requirement
structure Scripted (p u:ℕ) (B:Marked M)(γ:ℝ): Prop where
 funding : Counselor G S u Y B γ
 bands : Spectrum S u Y B.age_f G
 minimum : p+2≤u
 tariff_p : Poly B.age_f (League.beginsP G S u Y)
 price_u : Poly B.age_f (spoolA S Y G u)
 tariff_v : Poly B.age_f (spoolB S Y G u)
 leg i j:i≤p+2→ j≤p+2→ Poly B.age_f (fun w=> Warm.disksL K (S.pactP w) G (Z _) i j u)
 arm i j:i≤p+2→ j≤p+2→ Poly B.age_f (fun w=> Warm.disksR K (S.pactP w) G (Z _) i j u)
 cold u' :1≤u' → u'+1≤ p+2→∀ w:Flap M, t_budget S Y G u u' w*(1+shareP G S u Y w.next)≤ B.coin (-γ) w

-- prove stat Poly pol tools
private lemma poly_prod {f:I→X→ℝ≥0∞}{M:Meter X}{a:Finset I}(h:∀ i∈a,Poly M (f i)): Poly M (fun x=>∏ k∈a,f k x):=by
 induction a using Finset.induction_on with
 | empty=>simp;exact Poly.oneQ _
 | insert k u hk ih=>simp_rw [prod_insert hk];exact (h _ (mem_insert_self ..)).mul (ih (fun k hk=>h k (mem_insert_of_mem hk)))
variable {B₁:Marked M} {γ:ℝ}
local notation "B"=> B₁.age_f
variable (C: Scripted S Y G Z p u B₁ γ)
include C
lemma shares_up : Poly B (fun i=>shareP G S u Y i.next):= renewed (Poly.us (C.funding.currency) Flap.next) (Marked.utilizes B₁ C.funding.capital)
lemma poll_t (r:ℕ): Poly B (t_budget S Y G u r):=by
 let θ:=fore_c G.ColorIndex r u (5-(r+1)); let g:= beginsP G S u Y; let D:= C.tariff_p
 have hv: Poly B (fun i=>θ (g i)):=by
    unfold θ fore_c
    have ht:(Fintype.card (Regalia G.ColorIndex):ℝ≥0∞)≠⊤:= by finiteness -- name
    have hf:ledger_c G.ColorIndex r u (5-(r+1))≠⊤:=by unfold ledger_c; have he:= limited_f (J:= Fin r × Axis) u (5-(r+1)); finiteness
    apply ((Poly.standard _ ht).mul D).mul (Poly.mul (?_) (Poly.standard _ hf))
    apply Poly.mul ?_ (Poly.standard _ (by finiteness))
    exact (Poly.standard _ (by finiteness : (1+r:ℝ≥0∞)^u≠⊤)).mul (D.powQ r)
 apply hv.mono; intro i; unfold t_budget;apply (mul_le_mul_right _ (θ (g i))).trans_eq (mul_one _);unfold award; rw [← inv_one (G:=ℝ≥0∞)]; exact ENNReal.inv_le_inv.mpr (by exact_mod_cast (S.sizeL i).property)
lemma poll_u (r:ℕ) : Poly B (sp_budget S Y G u r):=by
 let θ:= fore_b G.ColorIndex r u (5-(r+1));let g:=beginsP G S u Y; let D:= C.tariff_p
 have hv : Poly B (fun i=>θ (g i)):=by
    unfold θ fore_b
    have ht:(Fintype.card (Regalia G.ColorIndex):ℝ≥0∞)≠⊤:=by finiteness
    have hf:ledger_d G.ColorIndex r (5-(r+1))≠⊤:=by unfold ledger_d; have he:= display_f (J:= Fin r × Axis) (5-(r+1));finiteness
    apply ((Poly.standard _ ht).mul D).mul (Poly.mul ?_ (Poly.standard _ hf))
    apply Poly.mul ?_ (Poly.standard _ (by finiteness))
    exact (Poly.standard _ (by finiteness : (1+r:ℝ≥0∞)^u≠⊤)).mul (D.powQ r)
 apply Poly.mul hv; apply Poly.powQ (p:=4); convert C.funding.capital.fromF using 1; ext1 i;rw [Marked.day, C.funding.shapeS,ENNReal.ofReal_natCast]

def starM (i:ℕ)(u:ℕ)(v:Flap M):= staff G u i (spoolA S Y G u v) (spoolB S Y G u v)
lemma printing (i): Poly B (starM S Y G i u):=by
 let a:= C.price_u;let b:= C.tariff_v
 unfold starM staff
 apply Poly.mul (Poly.standard _ (by have hx:=Gain.hatch_fin G i; finiteness));apply Poly.powQ; unfold surf
 exact (a.add ((Poly.standard _ (by finiteness : (2:ℝ≥0∞)^u≠⊤)).mul b)).add ((a.mul (Poly.standard _ (by finiteness))).add ((b.mul (Poly.standard _ (by finiteness))).mul (Poly.standard _ (by finiteness))))
lemma taxes (e r:ℕ) : Poly B fun i=> taxation e r (fun j=>starM S Y G j u i):=by apply Poly.sum; intro j _; apply Poly.sum; intro k _; apply Poly.sum; intro g _; apply poly_prod;intro z _;exact printing S Y G Z C _
omit C Z -- possible
lemma living_v (p:ℕ) (i:Flap M)(h:S.l i.prev ≤ S.l i.next) : Curves (Gain.halo (Z₁ i) (Z₂ i)) (Tariff.native (S.l i.next) (S.l_p i.next) u) (localL (S.l i.prev)) (localL (S.l i.next)) p (starM S Y G p u i):= Skein.published (S.l_p _) h p (merited S Y G u i)
-- h parameter clipping.T.need witness. Merit coherence.
end YM.RegulatorIR.Venture
