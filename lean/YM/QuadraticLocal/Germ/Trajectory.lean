import YM.QuadraticLocal.Corner
import YM.QuadraticLocal.Germ.Client
/-!
# Collared-mark passive steps on this same trajectory

 Actual repeated admission with physical test protocol and old root set inventory.
 Summability of true projected K exact polynomial after injective nook expansion paid
 through unmarked comparison `h.earns`. Thus Atlas.Every full.Mode across all stencils
 and tests not just ⋆. Unions of P rooted hulls may still require period.Wrap bookkeeping
 and registration; this proves exact & qforce and exposure **on the torus with every
 step's budget** unshortened. No collapsing preimages or normalizing by free-period vacuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "Ta"=> R.T
local notation "Sz"=> R.metals.p
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
local notation "c"=> R.family.side
variable {m n i b q k N:ℕ} (h:WayStation R.kit) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "L"=> R.rolls.L Y
local notation "X"=> R.alloy.B.a.budget i
local notation "W"=> R.alloy.B.a.budget (i+1)
local notation "xd"=> Φ i
local notation "γ"=> Φ (i+1)
local notation "Vd"=> (Φ i)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
variable (l:m≤ i)
local notation "P"=> Ψ (i+1)
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
open Marker
namespace Relay
variable {u d f:ℕ} {a α β : ℝ}
variable {Θ:Type}[DecidableEq Θ]{J:Marker.Census Θ}
variable {Yx:Θ→Type} [∀ i,AddCommGroup (Yx i)] [∀ i,Module ℂ (Yx i)]
variable (Ax:∀ i, Set (Yx i)) (K:∀ i, Submodule ℂ (Yx i)) (D0:Affinity.Spring ℝ Ax)(hA:∀ i:Θ, Set.MapsTo (fun t:Yx i=> Complex.I • t) (Ax i) (Ax i))
local notation "Y!"=> Affinity.Full (E:=Yx)
local notation "A!"=> (Affinity.Wallet Ax)
-- pull model stencils to full protocols
section Frame
def dict {c':Side}{ox:Θ→Site c'}{Px:RG.Rep G c'} (XY:Estate (Affinity.Full (E:=Yx)) ox Px J):Estate (Affinity.Wallet Ax) ox Px J:= {locale:=XY.locale,seats:=XY.seats,canvas:= Affinity.readH XY.canvas (Affinity.readBack Ax)} -- notation A shadows
end Frame
variable {o':Θ→ Site (R.family.side (i+1) n)}
variable {a':Θ→ Site (R.family.side i n)}
local notation "D!"=> Estate (Y!) o' P J
variable (Tx: Θ→Support (R.family.side (i+1) n))
variable (E: Estate (Affinity.Full (E:=Yx)) o' (Ψ (i+1)) J)
variable (hl: q ≤ R.alloy.B.a.clock.J i)(r:i<N)(hw:∀ u:J.Mode,u.val.card≤q)
variable (w:Θ→ℝ) (hφ:∀ i,0<w i)
include h r v K₀ l hl hw hφ
variable (hX: Affinity.Adult Tx K E.canvas) (hI: (Affinity.readH E.canvas (Affinity.readBack Ax)).Pays w ((Ψ (i+1)).p.supportExponent) 1 1)
local notation "o!"=> (R.family.path.levels.clock.op i n).ratio.parent
local notation "FullPush"=> Integration.LocalComparison.actualPush Z N n i
local notation "C"=> Estate (Y!) (o! ∘ o') (P') J
local notation "Σ*"=> fun x=>(Tx x).image o!
variable [Nonempty (Affinity.Wallet Ax)][Fintype Θ]
include D0 Ax K Tx hX hA hI
open Affinity
lemma branch : ∃ x:C, (∀ t:Y!, FullPush (E.canvas.density t)=x.canvas.density t) ∧ Adult Σ* K x.canvas ∧ (readH x.canvas (readBack Ax)).Pays w ((Ψ i).p.supportExponent) (budgetR R i) wp:=by
   obtain ⟨U,hU,⟨WC⟩⟩:= (v.2 i l r).earns; obtain ⟨Wq,y,bω,hT⟩:= h.frost.license _ _ (step_paid S i) q I hl le_rfl (show 1≤ I from (by have hm:= (S).clock.adm i; omega))
   let P₁:=hT (Φ i) (R.alloy.B.valid.pays i); obtain ⟨ER,he⟩:= invited R h D Q π Γ Ψ v K₀ l r I U P₁; obtain ⟨w'⟩:= Travel.sealed _ _ hI
   let θ' := (Classical.arbitrary A!); have hXs:= (later R π Γ Ψ v (Nat.le_succ_of_le l) r); have hy:=(later R π Γ Ψ v l r.le); have hP: (P').eval=(τ).push (P).beta (P).eval := (v.1.visit i l r).ident; have hP' : ∀ U',(P').eval U'≠0:= fun U'=> (congr_fun hy.view U').symm ▸ (YM.Multi.AxisShift.chosen_positive R.makes.wilson r.le U').ne'
   obtain ⟨I0,h0,Xs,he',hp,hτ⟩ := Travel.Client.recovery U WC ER Ax K E.canvas w w' hφ (spare R π Γ Ψ v (Nat.le_succ_of_le l) r) hw (by norm_num) θ' Tx hX D0 hA (Willow.spare_pos _).le hP' hP (Classical.choice (Tree.select (τ).ratio ((τ).patch.odd_side)))
   let θ := (Ψ i).p.supportExponent+1+1; let y':=y; let X' := Spire.fees ((τ).ratio.count) θ+(y (Φ i))^q*bω (Φ i)
   have hv : X' ≤ budgetR R i := by
      unfold budgetR; unfold X' θ; rw [show (τ).ratio.count=L from U.laws.data.funds.length_eq, show (Ψ i).p.supportExponent=(R.metals.p.profile (R.alloy.B.a.clock.J i)).supportExponent from (congr_arg BudgetPoint.supportExponent (show (Ψ i).p=X from hy.truep.point)).trans (congr_arg RG.Stage.supportExponent (PriceCompiler.params_eq R.alloy.B.valid i)),PriceCompiler.beta_eq R.alloy.B.valid i]; exact le_min (P₁.geom.trans P₁.growth) P₁.lightBand
   let x:C:= { locale:= I0,seats:=h0,canvas:=Xs }
   rw [mul_one] at hp; have hy: (readH x.canvas (readBack Ax)).Pays w ((Ψ i).p.supportExponent) X' wp:=hp
   refine ⟨x,fun t=>?_,he',⟨Lamps.loan_monotone _ hy.budget hv,hy.wages⟩⟩
   unfold Integration.LocalComparison.actualPush; rw [show R.family.path.β N n (i+1)=(P).beta from hXs.beta.symm]; exact hτ t
omit h r v K₀ l hl hw hφ D0 Ax K Tx hX hA hI
section Globe
open PaceR
variable {s:ℕ}{ε:ℝ}
variable (o:(i:ℕ)→ Θ→Site (R.family.side i n))
variable (T:(i:ℕ)→ Θ→Support (R.family.side i n))
variable (hr:∀ i,m ≤ i → i < b → o i=(R.family.path.levels.clock.op i n).ratio.parent ∘ o (i+1))
variable (he:∀ i,m ≤ i → i < b → T i=(fun v=> (T (i+1) v).image (R.family.path.levels.clock.op i n).ratio.parent))
variable (Eₜ:Estate (Affinity.Full (E:=Yx)) (o b) (Ψ b) J)
variable (hH: Affinity.Adult (T b) K Eₜ.canvas) (h':(dict Ax Eₜ).canvas.Pays w (Ψ b).p.supportExponent 1 1)
variable (T' :∀ i,s≤ i→i≤b→ Estate (Affinity.Full (E:=Yx)) (o i) (Ψ i) J)
set_option quotPrecheck false
local notation "toll"=> fun i=> Stoop.radius w (roof R i b)
local notation "E!"=> fun i=> Estate (Y!) (o i) (Ψ i) J
structure TreeHouse (s:ℕ) (T':∀ i,s≤ i→i≤b→ Estate (Affinity.Full (E:=Yx)) (o i) (Ψ i) J) : Prop where
    head : s ≤ b
    stays : T' b head (le_refl _) = Eₜ
    carries i (hi:s≤ i)(hu:i≤ b): Adult (T i) K (T' i hi hu).canvas
    bills i (hi:s ≤ i) (hz:i≤b): (dict Ax (T' i hi hz)).canvas.Pays (toll i) (Ψ i).p.supportExponent 1 1
    historyP i (hi:s ≤ i)(hu:i<b): pocket R (N:=N) Ψ (dict Ax (T' i hi hu.le)) (dict Ax (T' (i+1) (Nat.le_succ_of_le hi) hu)) (toll (i+1))
    tall i (hi:s ≤ i)(hu:i<b): ∀ t, Integration.LocalComparison.actualPush Z N n i ((T' (i+1) (Nat.le_succ_of_le hi) hu).canvas.density t)=(T' i hi hu.le).canvas.density t
include Ax K
lemma utter (hH:TreeHouse R (N:=N) Ψ Ax K w o T Eₜ s T'): Atlas (N:=N) R Ψ w o (dict Ax Eₜ) s (fun i h p=>dict Ax (T' i h p)):=⟨hH.head,congr_arg _ hH.stays,hH.bills,hH.historyP⟩ -- order check
include hr he hφ h v K₀ D0 hA hw
include l r hl
omit hr he in
private lemma named (x:E! (i+1))(E:Θ→ Site (R.family.side i n))(V':Θ→ Support (R.family.side i n)) (he:E=o! ∘ o (i+1))(hT:V'=fun v=> (T (i+1) v).image o!) (hv: Adult (T (i+1)) K x.canvas)(hE:(dict Ax x).canvas.Pays w ((Ψ (i+1)).p.supportExponent) 1 1) : ∃ y: Estate Y! E (P') J, (∀ t, FullPush (x.canvas.density t)=y.canvas.density t) ∧ Adult V' K y.canvas ∧ (dict Ax y).canvas.Pays w ((Ψ i).p.supportExponent) (budgetR R i) wp:=by subst E V'; exact branch R h D Q π Γ Ψ v K₀ l Ax K D0 hA (T (i+1)) x hl r hw w hφ hv hE
omit r l hl
variable (hℓ:q ≤ R.alloy.B.a.clock.J m)(hb:b≤ N)
include hH h' hb hℓ
lemma lives (hmi:m≤ i)(hi:i≤b): ∃ T',TreeHouse R (N:=N) Ψ Ax K w o T Eₜ i T':=by
   induction hi using Nat.decreasingInduction with
   | self=>
      let T' (i:ℕ) (h:b≤ i)(hr:i≤b): E! i:= (Nat.le_antisymm h hr) ▸ Eₜ; refine ⟨T',le_rfl,rfl,fun i hi hz=>?_,fun i hi hz=>?_,fun i hi hj=> by omega, fun i hi hj=> by omega⟩
      · have he:= Nat.le_antisymm hi hz; subst i; exact hH
      have hv:= Nat.le_antisymm hz hi; subst i; dsimp only []; rw [show Stoop.radius w (roof R b b)=w from funext (fun x=> by unfold roof Stoop.radius; simp)]; exact h'
   | of_succ i hx ih=>
      obtain ⟨U',hU⟩:= ih (Nat.le_succ_of_le hmi); obtain ⟨Z',hD,hτ,hP⟩:= named R h D Q π Γ Ψ v K₀ hmi Ax K D0 hA (hℓ.trans ((S).fits.mono hmi)) (lt_of_lt_of_le hx hb) hw (toll (i+1)) (health w hφ R b (i+1)) o T (U' _ le_rfl hx) _ _ (hr i hmi hx) (he i hmi hx) (hU.carries _ le_rfl hx) (hU.bills _ le_rfl hx)
      let Q' (j:ℕ)(hi:i≤j)(he:j≤b) : E! j := if hp:i<j then U' j hp he else (le_antisymm hi (Nat.le_of_not_gt hp)) ▸ Z'
      have hh : Q' i le_rfl hx.le=Z':= dif_neg (by omega : ¬i < i)
      have hh' j (h:i<j)(hy:j≤b) : Q' j h.le hy=U' j h hy:= dif_pos h
      have hc : pocket (N:=N) R Ψ (dict Ax Z') (dict Ax (U' (i+1) le_rfl hx)) (toll (i+1)):=⟨hP,fun t=> (hD (Affinity.readBack Ax t)).symm⟩
      refine ⟨Q',hx.le,(hh' b hx le_rfl).trans hU.stays,fun j h hz=>?_, fun j hj hz=>?_,fun j hj hz=>?_,fun j hj hz=>?_⟩
      · 
        rcases eq_or_lt_of_le h with hi|hi; · subst j; rw [hh]; exact hτ
        rw [hh' j hi hz]; exact hU.carries _ hi hz
      · rcases eq_or_lt_of_le hj with hi|hi; · subst j; rw [hh]; dsimp only []; rw [old R w hx]; exact capacious R h π Γ Ψ v hmi _ (health w hφ R b (i+1)) (lt_of_lt_of_le hx hb) hc
        rw [hh' j hi hz]; exact hU.bills _ hi hz
      · rcases eq_or_lt_of_le hj with hi|hi; · subst j; rw [hh,hh' (i+1) (by omega) hz]; exact hc
        rw [hh' j hi hz.le,hh' (j+1) (by omega) hz]; exact hU.historyP j hi hz
      rcases eq_or_lt_of_le hj with hi|hi; · subst j; rw [hh,hh' (i+1) (by omega) hz]; exact hD
      rw [hh' j hi hz.le,hh' (j+1) (by omega) hz]; exact hU.tall j hi hz
end Globe
end Relay
end YM.QuadraticLocal.Advent
