import YM.SignedWilsonExpansion.F9.Dune
/-!
# Costs on insertion containers

Being Auth means having *all* senses, the credit is needed in epochs
only for finite orders at a time. Update invoices with dimension through
`Page.Y`; the weight η may be taken 0 unless stated explicitly.
-/
set_option autoImplicit false
set_option maxHeartbeats 705000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{e s k h m c v T N M i j l r p u :ℕ}
variable {B Q D Z X Y η t a:ℝ}{E W U:Credit}
local notation "Fz" => PowerSeries.X
/-- All calendar bounds *at variable of the corresponding level* -/
structure Respect (k e u:ℕ)(t:ℝ)(P:Era G ℝ)(Z:ℝ): Prop where
   auth : Auth k P
   face : Saturation e 0 u P.2 t Z
variable {P P' R':Era G ℝ}{R: Realm G (e+1) E}
namespace Respect
variable (f:Respect k e u t P Z)
include f
lemma nn :0≤Z:= (f.face 0 (Nat.zero_le e) 0 (by omega)).C
lemma rise (q: Z≤X) : Respect k e u t P X:=⟨f.auth,fun i p j v=>(f.face i p j v).more q⟩
lemma grow (p:k≤l):Respect l e u t P Z:=⟨f.auth.tall p,f.face⟩
lemma anchor :∀ i≤ e,∀ r, Fruit 0 t u (P.2 i r) Z:=fun i v r=> f.face i v r (Nat.zero_le _)
lemma flush : Flush e u t P Z:=⟨f.nn,f.face⟩
lemma paired (q:0≤Q):Fringed k e u t Z Q P P:= Fringed.same f.flush f.auth q
lemma care {o:Cover}(hz:t≥0): Respect k e 0 0 (shifted P o) Z :=by
   refine ⟨f.auth.shifted o,fun i p j v=>?_⟩ -- need t≥0
   have ht:= f.anchor i p j
   have hv:= ((ht.shave le_rfl hz).slice (le_refl 0) (Nat.zero_le u)).turn o
   let z:=hedge (α:=Hooks G) 0 0 0 (r:=j); have hh: z= hedge (α:=Hooks G) o 0 0 (r:=j):= funext fun _=>by simp only [z,hedge,autumn,pow_zero]
   change Award (revolve o (P.2 i j)) z Z; rw [hh]; simpa only [add_zero,Fruit] using hv
lemma series (d:ℝ): Respect k e u t (d • P) (|d| * Z):=⟨f.auth.μ _,fun i p j v=>(f.face i p j v).μ _⟩
lemma add (q:Respect k e u t P' B)(v:0≤t): Respect k e u t (P+P') (Z+B):=⟨f.auth.add q.auth,fun i p j h=> (f.face i p j h).plus (q.face i p j h) v⟩
lemma diff (q:Respect k e u t P' B)(v:0≤t): Respect k e u t (P-P') (Z+B):=⟨f.auth.sub q.auth,fun i p j h=> (f.face i p j h).diff (q.face i p j h) v⟩
lemma shaved (v:0≤a)(p:a≤ t)(z:j≤u) :Respect k e j a P Z:=⟨f.auth,fun i v' j p'=> ((f.face i v' j p').shave v p).slice v z⟩
-- measuring trimmed columns after formal cost substitution on their clock
lemma fixed (x:Cost)(q:FitS e x B)(v:0≤t): Respect k e u t (trim x P) ((e+1:ℕ)*(B*Z)):=by
    refine ⟨trim_auth _ f.auth,fun i p j h=>?_⟩; let S:=Finset.antidiagonal i; have hp (a) (hp:a∈S): Fruit 0 t u (coeff a.1 x • P.2 a.2 j) (B*Z):=by
       have he:= Finset.mem_antidiagonal.mp hp; exact (((f.anchor a.2 (by omega) j).μ _).more (mul_le_mul_of_nonneg_right (q a.1 (by omega)) f.nn))
    simp only [trim, affix, Finset.sum_apply,Pi.smul_apply]; let hC := Fruit.sum (S:=S) hp v -- parse
    apply hC.more; rw [Finset.sum_const, nsmul_eq_mul,Finset.Nat.card_antidiagonal]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show i+1≤e+1 by omega)) (mul_nonneg q.nn f.nn)
lemma mat (u':Respect l e u t P' X) (Q:0≤ t) (p:k+l ≤ i) : Respect (k+l) e u t (agateV P P') (coinMat i e*Z*X) :=by
    let z:= fringedMat (f.paired (Q:=0) le_rfl) (u'.paired le_rfl) Q p
    exact ⟨z.inkV,z.f_l.2⟩
omit f
lemma stock (h:Fringed k e u t B Q P P') : Respect k e u t P B∧ Respect k e u t (P-P') (B*Q):=⟨⟨h.inkV,h.f_l.2⟩,⟨h.inkV.sub h.pen,fun i p j _=>(h.heapS i j p).toll⟩⟩
lemma zero : Respect k e u t (0:Era G ℝ) 0:=by
    exact (stock (Fringed.nullV (δ:=0) le_rfl le_rfl)).1
lemma sum {J:Type*}(S: Finset J)(P:J→Era G ℝ)(B:J→ℝ)(u':∀ i∈S,Respect k e u t (P i) (B i))(v:0≤t): Respect k e u t (∑ i∈S,P i) (∑ i∈ S,B i):=by
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact zero
   | @insert i S p ih=> rw [Finset.sum_insert p,Finset.sum_insert p]; exact (u' i (Finset.mem_insert_self ..)).add (ih (fun i u=>u' i (Finset.mem_insert_of_mem u))) v
lemma fixtures {n:ℕ} (P:Fin (n+1)→Era G ℝ)(B:Fin (n+1)→ℝ)(K:Fin (n+1)→ℕ) (v:0≤t)(p: (∑ i,K i)≤ l)(h:∀ i, Respect (K i) e u t (P i) (B i)) : Respect (∑ i,K i) e u t (MassP G ℝ n P) ((coinMat l e)^n*∏ i,B i):=by
    rw [←loadRep]; let U:= valueP n P P K B p (fun i=>(h i).paired (Q:=0) le_rfl) v; exact (stock U).1
end Respect

-- generic bills per age Crop.Gate. Budget independent of anchor set.
def cabin (G:Gauge)(k e u:ℕ)(E W:Credit):= (bulkCert G k e u E W).choose
def westW (G:Gauge)(k e u:ℕ)(E W:Credit):= (beamGo G k e u E W).choose
def windy (G:Gauge)(k e u:ℕ)(E W:Credit):= (waveSeen G k e u E W).choose
variable (d:Dormitory R k u W)(g:Canopy R m c Z)(ξ:ℕ→ℝ)(w:Escort R m c ξ)
include d g w
lemma voyage (v:c≤N)(f:Respect k e u (ξ c) P B): Respect k e u (ξ m) (cruises R.draws R.paid N k c m P) ((cabin G k e u E W).buy Z*B):=⟨cruising R.draws R.hG R.green g.order v f.auth,fun i p j t=>(bulkCert G k e u E W).choose_spec i p j R d m c ξ N Z w g.pad v P B f.auth f.nn f.face⟩
lemma memory (v:c≤N) (f:Respect k e u (ξ c) P B): Respect k e u (ξ m) (axeR (cruises R.draws R.paid N k c m P)) ((westW G k e u E W).buy Z*R.tempC m c*B):=by
    refine ⟨(cruising R.draws R.hG R.green g.order v f.auth).axe,fun i p j t=>?_⟩; let K:= westW G k e u E W; cases j with
    | zero=> simp only [axeR,lop,if_true]; exact Fruit.zero.more (mul_nonneg (mul_nonneg (zero_le_one.trans (K.purchase g.positive)) (trail_pos ..).le) f.nn)
    | succ j=> simp only [axeR,lop,if_neg (by omega : j+1 ≠ 0)]; let hB:= (beamGo G k e u E W).choose_spec i p (j+1) R d m c ξ w N P B f.auth v f.nn (fun i p j _=>f.anchor i p j) (by omega); exact hB.more (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (g.older K (le_refl _) g.order) (trail_pos ..).le) f.nn)
lemma recalled (b:ℕ)(u':c≤ b)(v:b≤ N)(t:b≤ M)(f:Respect k e u (ξ c) P B): Respect k e u (ξ m) (cruises R.draws R.paid N k c m P-cruises R.draws R.paid M k c m P) ((windy G k e u E W).buy Z*B*R.tempC c b):=by
    exact (Respect.stock ((waveSeen G k e u E W).choose_spec R d m c ξ b N M B _ Z w g.pad u' v t le_rfl P P (f.paired (trail_pos ..).le))).2
end YM.WilsonCoeffUV.Mer.Xa
