import YM.FVAAlt2.Home.Price
/-!
# Applying the matrix at all points of a profile. Re-expression of
 `Plan.begins`. The move is *finite-regulator exact*, from same `Local.Section` and `full` denominator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home
open Function Set Finset Filter Topology Lattice
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open Precision Extra.FD Maxwell Labels Extraction
open MS MS.Local.Physical MS.Koszul MS.Menus MS.Book MS.Plane MS.Theater
open MeasureTheory
open RG10.Position (Plan Spur Loft owner)
open PowerSeries (C coeff constantCoeff)
open Profiles
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {G:Gauge}{L:Frames G}{B:Deck G}
variable {J W:Type*} {Q:E4} {H:Source.Hol G} {K:Test 1} {d r:ℕ}
variable (R:Lobby.Registry L H) (D: ChartRatio G)(q:ℕ+) (m d':ℕ)
set_option linter.unusedSectionVars false
local notation "F"=> Glyph B d
local notation "Y"=> RG10.Position.Deck L d
local notation "KX"=> MS.Land.Plaid
local notation "PSc"=> PowerSeries ℂ
local notation "PS"=> PowerSeries ℝ
local notation "rV"=> RG10.Position.Deck.token
local notation "C₀"=> carryΩ L
local notation "r₄"=> ℂ
-- input i: Glyph, allow only same height deck in expansion
lemma parent_of {h: ℕ}{y:Spur L h}(he:h≤d): RG10.Position.owner (RG10.Position.Deck.token L d (carryΩ L he (realToken L y)))= RG10.Position.deck L h ( realToken L y ):= by rfl -- unused args implicit issue
abbrev ownCoord (i:Glyph B d): KX B i.size:= i.2
abbrev canon (x:Datum J): (Fin x.1.n→E4)→ℝ:= fun v => (x.1.test (YM.points v)).re
lemma lampu (i:Glyph B d) (he : i.size≤d) : i=up he (MS.Land.read (ownCoord i)):= by obtain ⟨⟨i,hi⟩,v⟩:=i;rfl
abbrev announcedL (i:Glyph B d): Label G i.size:= Shop.seat B i.2.2
lemma pop_owns (i:MS.Land.Plaid B d): popTag (Lobby.owner (MS.Land.read i))=announcedL (MS.Land.read i):=rfl

def mintC (p:Datum F):= visit q m (canon p) (fun x:Fin p.1.n→Native q m=> Lobby.Paid D R x (epsilon q m) (Lobby.owner ∘ p.2))
-- natural (still) line torus: shape input. deploy `curve` at lifted horizon. specify heights.
lemma minted (p:Datum F): mintC R D q m p=curve R D q m (canon p) (fun i=>(p.2 i).size) (fun i=>announcedL (p.2 i)):= rfl
variable (L)(B)
-- height preserving row crossing.A.S.H(H-dual)
def readC (d:ℕ): Matrix (Glyph B d) (RG10.Position.Deck L d) (PowerSeries ℂ) := (Φin L B d).map PowerSeries.C
def overΩ (d:ℕ): Matrix (RG10.Position.Deck L d) (Glyph B d) (PowerSeries ℂ):= (Φout L B d).map PowerSeries.C
lemma restoreC(d:ℕ): readC L B d * overΩ L B d=1:= by rw [readC,overΩ,← Matrix.map_mul, Φlin,Matrix.map_one]<;> simp; -- check gens
lemma intoC(d:ℕ): overΩ L B d * readC L B d=1:= by rw [readC,overΩ,← Matrix.map_mul, Φlout,Matrix.map_one]<;> simp
lemma refu(i: Glyph B d)(he:i.size≤d)(k: Spur L i.size) : Ωc L B i (C₀ he ( realToken L k )) = Ωc L B ( MS.Land.read (ownCoord i) ) (realToken L k):= by
    obtain hx:= raised_c L B (MS.Land.read (ownCoord i)) ( realToken L k ) he; rwa [ ← lampu i he] at hx
-- keys X(coeff basis per slot in height; no Pa Domain assumption). Exact row D & Epoch continuity later.
variable {L B}
variable (P:Plan L) (hD:LocalRatio D)
local notation "β"=> seats P.liftOff P.certified
local notation "Π"=> FormalOPE.RG10.Position.Deck L
lemma off_w (i : Glyph β d): ∑ k:Spur L i.size, Ωc L β ( MS.Land.read (ownCoord i) ) (realToken L k) • P.liftOff.lift i.size ( RG10.Position.deck L i.size ( realToken L k ) )=announcedL i:=by
 let s:=i.size; have he: projector P.liftOff s (announcedL i)= announcedL i:= loft_from P.liftOff P.certified (i.2.2)
 rw [← he,projector, LinearMap.comp_apply, ← show mast β s L (MS.Land.read (ownCoord i))=sourceAt L s (announcedL i) from pegl (ownCoord i)] -- maybe defeq
 rw [← level_reverse L β (ownCoord i)]; rw [map_sum]; exact sum_congr rfl fun i hi=> (map_smul ..).symm
-- ω lifted glyph→Deck exact owner weights formula. All profiles PSD reading yes. Career.
include hD
lemma initialMS : mintC (B:=β) (d:=d) (nativeR P) D q m = mix (into ∘ P.begins q m d) (readC L β d) := by
 funext w; rcases w with ⟨x,F₁⟩; let f(i:Fin x.n):= (F₁ i).size; have hf(i: Fin x.n): f i≤d:= Nat.le_of_lt_succ (F₁ i).1.isLt; let t(n:Fin x.n)(p:Spur L (f n)):=C₀ (hf n) (realToken L p)
 symm; rw [monoread ( U:=fun n:Fin x.n=> Spur L (f n) ) (J:=t)]; rotate_left
 · exact fun i j k h=> eq_of_heq (Sigma.mk.inj h).2
 · intro i k hk; change PowerSeries.C _=0; rw [show Φin _ _ _ _ _=0 from cite_c _ _ _ k (fun ht=>?_ ), map_zero ]; obtain ⟨⟨n,h⟩,u⟩:=k; have hy:n=f i:=congr_arg Prod.fst ht; subst n; exact hk ⟨u,rfl⟩
 rw [minted];
 let V(j:Fin x.n):=announcedL (F₁ j); let r (j:Fin x.n) (i:Spur L (f j)) := Ωc L β (MS.Land.read (ownCoord (F₁ j))) (realToken L i); let Y'(j:Fin x.n)(i:Spur L (f j)) := P.liftOff.lift (f j) (RG10.Position.deck L (f j) (realToken L i))
 change _= curve (nativeR P) D q m (fun v=> (x.test (YM.points v)).re) f V; rw [funext (fun i=> show V i= ∑ j,r i j • Y' i j from Eq.symm (off_w P (F₁ i))),distributes]; refine Finset.sum_congr rfl fun u _=>?_ ; unfold readC Φin; simp_rw [Matrix.map_apply, ← map_prod, Function.comp_apply ]; rw [mul_comm (PowerSeries.C _), ← agreement D q m P _ hD]; refine congr_arg₂ (· * ·) rfl ?_; congr 1; exact Finset.prod_congr rfl (fun i _=> refu L β (F₁ i) _ _) -- orientation
end YM.FVAAlt2.Home
